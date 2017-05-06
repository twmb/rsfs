//! An in memory filesystem.
//!
//! The [`FS`] provides an in memory file system. This implementation, only available on Unix
//! systems, implements all [`unix_ext`] traits. Errors returned mimic true Unix error codes via
//! the [`errors`] crate (which may not have the proper error codes for _all_ possible Unix systems
//! yet).
//!
//! All API calls to FS operate under a mutex to ensure consistency. Reads to [`File`]s can be
//! concurrent.
//!
//! # Example
//!
//! ```
//! use std::ffi::OsString;
//! use std::io::{Read, Seek, SeekFrom, Write};
//! use std::path::PathBuf;
//!
//! use rsfs::*;
//! use rsfs::unix_ext::*;
//! use rsfs::mem::fs::FS;
//!
//! // setup a few directories
//!
//! let fs = FS::with_mode(0o300);
//! assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());
//!
//! // open a file, write to it, and read from it
//!
//! let mut wf = fs.new_openopts().mode(0o600).write(true).create_new(true).open("a/f").unwrap();
//! assert_eq!(wf.write(vec![0, 1, 2, 3, 4, 5].as_slice()).unwrap(), 6);
//!
//! let mut rf = fs.new_openopts().read(true).open("a/f").unwrap();
//! assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);
//!
//! let mut output = [0u8; 4];
//! assert_eq!(rf.read(&mut output).unwrap(), 4);
//! assert_eq!(&output, &[1, 2, 3, 4]);
//!
//! // read a directory
//!
//! let mut reader = fs.read_dir("a").unwrap();
//!
//! let next = reader.next().unwrap().unwrap();
//! assert_eq!(next.file_name(), OsString::from("b"));
//! assert_eq!(next.path(), PathBuf::from("a/b"));
//!
//! let next = reader.next().unwrap().unwrap();
//! assert_eq!(next.file_name(), OsString::from("f"));
//! assert_eq!(next.path(), PathBuf::from("a/f"));
//!
//! assert!(reader.next().is_none());
//! ```
//!
//! [`FS`]: struct.FS.html
//! [`unix_ext`]: ../unix_ext/index.html
//! [`errors`]: ../errors/index.html

extern crate parking_lot;

use std::cmp::{self, Ordering};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ffi::OsString;
use std::io::{Error, ErrorKind, Read, Result, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Weak};
use std::vec::IntoIter;

use self::parking_lot::{Mutex, RwLock};

use errors::*;
use fs::{self, FileType as FTG, Metadata as MG};
use path_parts::{self, IteratorExt, Part};
use unix_ext::{self, PermissionsExt as PEG};

// TODO File could be tested more, maybe, but the raw_file seems sufficient.
// Permissions and FileType can be tested directly - right now they are tested indirectly.

// DIRLEN is the length returned from Metadata's len() call for a directory. This is pulled from
// the initial file size that Unix uses for a directory sector. This module does not attempt to
// return a larger number if the directory contains many children with long names.
const DIRLEN: u64 = 4096;

/// A builder used to create directories in various manners.
///
/// See the module [documentation] for a comprehensive example.
///
/// [documentation]: index.html
#[derive(Debug)]
pub struct DirBuilder {
    recursive: bool,
    mode: u32,
    fs: FS,
}

impl fs::DirBuilder for DirBuilder {
    fn recursive(&mut self, recursive: bool) -> &mut Self {
        self.recursive = recursive;
        self
    }
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        if self.recursive {
            self.fs.inner.lock().create_dir_all(path, self.mode)
        } else {
            self.fs.inner.lock().mkdir(path, self.mode)
        }
    }
}

impl unix_ext::DirBuilderExt for DirBuilder {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.mode = mode;
        self
    }
}

/// Entries returned by the [`ReadDir`] iterator.
///
/// See the module [documentation] for a comprehensive example.
///
/// [`ReadDir`]: struct.ReadDir.html
/// [documentation]: index.html
#[derive(Debug, PartialEq)]
pub struct DirEntry {
    dir: PathBuf,
    base: OsString,
    meta: Metadata,
}

impl fs::DirEntry for DirEntry {
    type Metadata = Metadata;
    type FileType = FileType;

    fn path(&self) -> PathBuf {
        self.dir.join(self.base.clone())
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        Ok(self.meta)
    }
    fn file_type(&self) -> Result<Self::FileType> {
        Ok(self.meta.file_type())
    }
    fn file_name(&self) -> OsString {
        self.base.clone()
    }
}

// `RawFile` is the underling contents of a file in our filesystem. `OpenOption`s `.open()` call
// returns a view of a file. If a file is removed from the filesystem, it is invalidated and all
// `File` views will fail (most) future operations.
#[derive(Debug)]
struct RawFile {
    valid: bool,
    data: Vec<u8>,
}

// append_at overwrites and appends bytes at a given existing index in a Vec.
fn append_at<T: Copy>(dst: &mut Vec<T>, at: usize, src: &[T]) {
    let end = src.len() + at;
    if dst.len() > end {
        dst[at..end].copy_from_slice(src);
    } else {
        dst.truncate(at);
        dst.extend_from_slice(src);
    }
}

impl RawFile {
    // read_at reads contents of the file into buf from a given existing index in the file.
    fn read_at(&self, at: usize, buf: &mut [u8]) -> Result<usize> {
        if !self.valid {
            return Err(ENOENT());
        }

        let src;
        let dst;

        let data = &self.data[at..];
        let buf_len = buf.len();

        match data.len().cmp(&buf_len) {
            Ordering::Less => {
                dst = &mut buf[..data.len()];
                src = data;
            }
            Ordering::Greater => {
                dst = buf;
                src = &data[..buf_len];
            }
            Ordering::Equal => {
                dst = buf;
                src = data;
            }
        }
        dst.copy_from_slice(src);
        Ok(dst.len())
    }

    // write_at writes to the RawFile at a given index, which must be at or less than `data.len()`.
    fn write_at(&mut self, at: usize, buf: &[u8]) -> Result<usize> {
        if !self.valid {
            return Err(ENOENT());
        }
        append_at(&mut self.data, at, buf);
        Ok(buf.len())
    }

    // invalidate ensures that all future operations on files will fail with ENOENT.
    fn invalidate(&mut self) {
        self.valid = false
    }
}

/// A view into a file on the filesystem.
///
/// An instance of `File` can be read or written to depending on the options it was opened with.
/// Files also implement `Seek` to alter the logical cursor position into the file (only `SeekFrom`
/// is currently implemented).
///
/// See the module [documentation] for a comprehensive example.
///
/// [documentation]: index.html
#[derive(Debug)]
pub struct File {
    read: bool,
    write: bool,
    append: bool,
    metadata: Metadata,
    file: Arc<RwLock<RawFile>>,
    at: usize,
}

impl fs::File for File {
    type Metadata = Metadata;

    fn metadata(&self) -> Result<Self::Metadata> {
        Ok(self.metadata)
    }
}

impl Read for File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        if !self.read {
            return Err(EBADF());
        }
        let res = self.file.read().read_at(self.at, buf);
        if let Ok(size) = res {
            self.at += size;
        }
        res
    }
}

impl Write for File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        if !self.write {
            return Err(EBADF());
        }
        let mut file = self.file.write();
        if self.append {
            self.at = file.data.len();
        }
        let res = file.write_at(self.at, buf);
        if let Ok(size) = res {
            self.at += size;
        }
        res
    }
    fn flush(&mut self) -> Result<()> {
        if !self.write {
            return Err(EBADF());
        }
        Ok(())
    }
}

impl Seek for File {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        match pos {
            SeekFrom::Start(offset) => {
                self.at = cmp::min(self.file.write().data.len(), offset as usize);
                Ok(offset)
            }
            _ => Err(Error::new(ErrorKind::Other, "only SeekFrom is implemented")),
        }
    }
}

/// Represents the type of a file.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct FileType {
    // TODO this is quite possibly the laziest implementation possible. It could be cleaner.
    dir: bool,
}

impl fs::FileType for FileType {
    fn is_dir(&self) -> bool {
        self.dir
    }
    fn is_file(&self) -> bool {
        !self.dir
    }
}

/// Metadata information about a file.
///
/// See the module [documentation] for a comprehensive example.
///
/// [documentation]: index.html
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Metadata {
    filetype: FileType,
    length: u64,
    perms: Permissions,
}

impl fs::Metadata for Metadata {
    type Permissions = Permissions;
    type FileType = FileType;

    fn file_type(&self) -> Self::FileType {
        self.filetype
    }
    fn is_dir(&self) -> bool {
        self.filetype.is_dir()
    }
    fn is_file(&self) -> bool {
        self.filetype.is_file()
    }
    fn len(&self) -> u64 {
        self.length
    }
    fn permissions(&self) -> Self::Permissions {
        self.perms
    }
}

/// Options and flags which can be used to configure how a file is opened.
///
/// See the module [documentation] for a comprehensive example.
///
/// [documentation]: index.html
#[derive(Clone, Debug)]
pub struct OpenOptions {
    read: bool,
    write: bool,
    append: bool,
    trunc: bool,
    create: bool,
    excl: bool,
    mode: u32,
    fs: FS,
}

impl fs::OpenOptions for OpenOptions {
    type File = File;

    fn read(&mut self, read: bool) -> &mut Self {
        self.read = read;
        self
    }
    fn write(&mut self, write: bool) -> &mut Self {
        self.write = write;
        self
    }
    fn append(&mut self, append: bool) -> &mut Self {
        self.append = append;
        self
    }
    fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.trunc = truncate;
        self
    }
    fn create(&mut self, create: bool) -> &mut Self {
        self.create = create;
        self
    }
    fn create_new(&mut self, create_new: bool) -> &mut Self {
        self.excl = create_new;
        self
    }
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        self.fs.inner.lock().open(path, self)
    }
}

impl unix_ext::OpenOptionsExt for OpenOptions {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.mode = mode;
        self
    }
}

/// Iterator over entries in a directory.
///
/// This is returned from the [`read_dir`] method of [`std::mem::FS`].
///
/// See the module [documentation] for a comprehensive example.
///
/// [`read_dir`]: struct.FS.html#method.read_dir
/// [`std::mem::FS`]: struct.FS.html
/// [documentation]: index.html
#[derive(Debug)]
pub struct ReadDir {
    ents: IntoIter<DirEntry>,
}

impl ReadDir {
    // read_dir on every system I have ever used returns dirents in alphabetical order, so we will
    // recreate that behavior here.
    fn new<P: AsRef<Path>>(path: P, dir: &Dirent) -> Result<ReadDir> {
        // read_dir is about the only call that needs read permissions (and remove_dir_all below,
        // but only because that does not use read_dir).
        if !dir.readable() {
            return Err(EACCES());
        }
        let children = dir.children.as_ref().ok_or_else(ENOTDIR)?;
        let mut dirents = Vec::new();
        for (base, dirent) in children.iter() {
            let dirent = dirent.read();
            dirents.push(DirEntry {
                dir: PathBuf::from(path.as_ref()),
                base: base.clone(),
                meta: || -> Metadata {
                    if dirent.is_dir() {
                        Metadata {
                            filetype: FileType { dir: true },
                            length: DIRLEN,
                            perms: Permissions::from_mode(dirent.mode),
                        }
                    } else {
                        Metadata {
                            filetype: FileType { dir: false },
                            length: dirent.file.as_ref().unwrap().read().data.len() as u64,
                            perms: Permissions::from_mode(dirent.mode),
                        }
                    }
                }(),
            });
        }
        dirents.sort_by(|l, r| match l.dir.cmp(&r.dir) {
            Ordering::Equal => l.base.cmp(&r.base),
            x => x,
        });
        Ok(ReadDir { ents: dirents.into_iter() })
    }
}

impl Iterator for ReadDir {
    type Item = Result<DirEntry>;

    fn next(&mut self) -> Option<Self::Item> {
        self.ents.next().map(Ok)
    }
}

/// Representation of the various permissions on a file.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Permissions {
    mode: u32,
}

impl fs::Permissions for Permissions {
    fn readonly(&self) -> bool {
        self.mode & 0o400 != 0
    }
    fn set_readonly(&mut self, readonly: bool) {
        if readonly {
            self.mode |= 0o400
        } else {
            self.mode &= !0o400
        }
    }
}

impl unix_ext::PermissionsExt for Permissions {
    fn mode(&self) -> u32 {
        self.mode
    }
    fn set_mode(&mut self, mode: u32) {
        self.mode = mode
    }
    fn from_mode(mode: u32) -> Self {
        Permissions { mode: mode }
    }
}

/// An in memory struct that satisfies [`rsfs::FS`].
///
/// `FS` is thread safe and copyable. It operates internally with an `Arc<Mutex<FileSystem>>`
/// (`FileSystem` not being exported) and forces all filesystem calls to go through the mutex. `FS`
/// attempts to mimic all real errors that could occur on a filesystem. Generally, unless you setup
/// an in memory system with low permissions, the only errors you could encounter would be from
/// performing operations on non-existing files or performing operations that expect non-existence.
///
/// See the module [documentation] for a comprehensive example.
///
/// [`rsfs::FS`]: ../trait.FS.html
/// [documentation]: index.html
#[derive(Clone, Debug)]
pub struct FS {
    inner: Arc<Mutex<FileSystem>>,
}

impl FS {
    /// Creates an empty `FS` with mode `0o777`.
    pub fn new() -> FS {
        Self::with_mode(0o777)
    }

    /// Creates an empty `FS` with the given mode.
    pub fn with_mode(mode: u32) -> FS {
        let pwd = Arc::new(RwLock::new(Dirent {
            mode: mode,
            file: None,
            parent: Weak::new(),
            children: Some(HashMap::new()),
        }));
        FS {
            inner: Arc::new(Mutex::new(FileSystem {
                root: pwd.clone(),
                pwd: pwd,
            })),
        }
    }

    /// Changes the current working directory of the filesystem.
    ///
    /// The directory being changed into must exist.
    ///
    /// # Example
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::unix_ext::*;
    /// use rsfs::mem::fs::FS;
    ///
    /// use std::ffi::OsString;
    /// use std::path::PathBuf;
    ///
    /// let fs = FS::new();
    /// assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());
    ///
    /// assert!(fs.cd("a/b").is_ok());
    ///
    /// let mut reader = fs.read_dir(".").unwrap();
    ///
    /// let next = reader.next().unwrap().unwrap();
    /// assert_eq!(next.file_name(), OsString::from("c"));
    /// assert_eq!(next.path(), PathBuf::from("./c"));
    ///
    /// assert!(reader.next().is_none());
    /// ```
    pub fn cd<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.inner.lock().cd(path)
    }
}

impl Default for FS {
    fn default() -> Self {
        FS::new()
    }
}

impl PartialEq for FS {
    fn eq(&self, other: &FS) -> bool {
        *self.inner.lock() == *other.inner.lock()
    }
}

impl fs::GenFS for FS {
    type DirBuilder = DirBuilder;
    type DirEntry = DirEntry;
    type Metadata = Metadata;
    type OpenOptions = OpenOptions;
    type Permissions = Permissions;
    type ReadDir = ReadDir;

    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Metadata> {
        self.inner.lock().metadata(path)
    }
    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<ReadDir> {
        self.inner.lock().read_dir(path)
    }
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.inner.lock().remove_dir(path)
    }
    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.inner.lock().remove_dir_all(path)
    }
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.inner.lock().remove_file(path)
    }
    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        self.inner.lock().rename(from, to)
    }
    fn set_permissions<P: AsRef<Path>>(&self, path: P, perm: Self::Permissions) -> Result<()> {
        self.inner.lock().set_permissions(path, perm.mode)
    }

    fn new_openopts(&self) -> OpenOptions {
        OpenOptions {
            read: false,
            write: false,
            append: false,
            trunc: false,
            create: false,
            excl: false,
            mode: 0o666, // default per unix_ext
            fs: self.clone(),
        }
    }
    fn new_dirbuilder(&self) -> DirBuilder {
        DirBuilder {
            recursive: false,
            mode: 0o777, // default per unix_ext
            fs: self.clone(),
        }
    }
}

// Dirent, which would be Dirent if DirEntry were not already taken, represents all information
// needed at a node in our filesystem tree.
//
// A Dirent is either a file OR a children, not both and not neither, but it seemed more
// uglier than it was worth to combine both of those into an enum.
#[derive(Debug)]
struct Dirent {
    mode: u32,

    file: Option<Arc<RwLock<RawFile>>>,

    parent: Weak<RwLock<Dirent>>,
    children: Option<HashMap<OsString, Arc<RwLock<Dirent>>>>,
}

impl Dirent {
    fn is_dir(&self) -> bool {
        self.file.is_none()
    }
    fn readable(&self) -> bool {
        self.mode & 0o400 > 0
    }
    fn writable(&self) -> bool {
        self.mode & 0o200 > 0
    }
    fn executable(&self) -> bool {
        self.mode & 0o100 > 0
    }
}

// FileSystem is a single in-memory filesystem that can be used cloned and passed around safely.
#[derive(Debug)]
struct FileSystem {
    root: Arc<RwLock<Dirent>>,
    pwd: Arc<RwLock<Dirent>>,
}

fn path_empty<P: AsRef<Path>>(path: P) -> bool {
    path.as_ref() == Path::new("")
}

// We claim that two filesystems are equal if they have they have the same structure and mode. This
// currently does not validate file contents.
impl PartialEq for FileSystem {
    fn eq(&self, other: &FileSystem) -> bool {
        fn eq_at(l: Arc<RwLock<Dirent>>, r: Arc<RwLock<Dirent>>) -> bool {
            let bl = l.read();
            let br = r.read();
            if bl.mode != br.mode {
                return false;
            }
            match (bl.file.is_some(), br.file.is_some()) {
                (true, true) => return true,
                (false, false) => (),
                _ => return false,
            }

            // Both must be directories here.
            let ch_l = bl.children.as_ref().unwrap();
            let ch_r = br.children.as_ref().unwrap();
            if ch_l.len() != ch_r.len() {
                return false;
            }
            for (child_name, cl) in ch_l.iter() {
                match ch_r.get(child_name) {
                    Some(cr) => {
                        if !eq_at(cl.clone(), cr.clone()) {
                            return false;
                        }
                    }
                    None => return false,
                }
            }
            true
        }

        eq_at(self.root.clone(), other.root.clone())
    }
}

impl FileSystem {
    // up_path traverses up parent directories in a normalized path, erroring if we cannot cd into
    // (exec) the parent directory.
    fn up_path(&self,
               parts: path_parts::Parts)
               -> Result<(Arc<RwLock<Dirent>>, path_parts::Parts)> {
        // If the parts begin at root, they will have no ParentDirs. We go up and return at root.
        if parts.at_root() {
            return Ok((self.root.clone(), parts));
        }

        // `up` is what we return: the Arc<Dirent> after traversing up all ParentDirs in `parts`.
        let mut up = self.pwd.clone();
        let mut parts_iter = parts.into_iter().peekable();
        while parts_iter.peek()
                        .and_then(|part| if *part == Part::ParentDir {
                            Some(())
                        } else {
                            None
                        })
                        .is_some() {
            parts_iter.next();
            if let Some(parent) = {
                let up = up.read();
                up.parent.upgrade().as_ref().cloned()
            } {
                if !parent.read().executable() {
                    return Err(EACCES());
                }
                up = parent;
            }
        }

        Ok((up, parts_iter.collect()))
    }

    // traverse goes up and down a path as necessary, returning the file system just before the
    // base of a path. Filesystem operations only require executable perms to lookup all
    // directories along a path for an operation, but the base of the path may require more
    // permissions.
    //
    // This returns an error if a directory we wanted to cd into is not executable (or if it is not
    // a directory).
    fn traverse(&self,
                parts: path_parts::Parts)
                -> Result<(Arc<RwLock<Dirent>>, Option<OsString>)> {
        let (mut fs, parts) = self.up_path(parts)?;
        let mut parts_iter = parts.into_iter().peek2able();
        while parts_iter.peek2().is_some() {
            if !fs.read().executable() {
                return Err(EACCES());
            }

            fs = {
                let fs = fs.read();
                let children = fs.children.as_ref().ok_or_else(ENOTDIR)?;
                children.get(parts_iter.next().unwrap().as_normal().unwrap())
                        .cloned()
                        .ok_or_else(ENOENT)?
            };
        }
        if !fs.read().is_dir() {
            return Err(ENOTDIR());
        }

        match parts_iter.next() {
            Some(Part::Normal(base)) => Ok((fs, Some(base))),
            _ => Ok((fs, None)),
        }
    }

    fn cd<P: AsRef<Path>>(&mut self, path: P) -> Result<()> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path))?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Ok(());
                } else {
                    self.pwd = fs;
                    return Ok(());
                }
            }
        };
        let borrow = fs.read();
        match borrow.children.as_ref().unwrap().get(&base) {
            Some(child) => {
                self.pwd = child.clone();
                Ok(())
            }
            None => Err(ENOENT()),
        }
    }

    fn set_permissions<P: AsRef<Path>>(&self, path: P, mode: u32) -> Result<()> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path))?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else {
                    fs.write().mode = mode;
                    return Ok(());
                }
            }
        };
        let borrow = fs.write();
        match borrow.children.as_ref().unwrap().get(&base) {
            Some(child) => {
                child.write().mode = mode;
                Ok(())
            }
            None => Err(ENOENT()),
        }
    }

    fn create_dir<P: AsRef<Path>>(&self, path: P, mode: u32, can_exist: bool) -> Result<()> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path))?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else {
                    if can_exist {
                        return Ok(());
                    }
                    return Err(EEXIST());
                }
            }
        };

        if !fs.read().executable() || !fs.read().writable() {
            return Err(EACCES());
        }

        let mut borrow = fs.write();
        match borrow.children.as_mut().unwrap().entry(base) {
            Entry::Occupied(o) => {
                if can_exist && o.get().read().is_dir() {
                    return Ok(());
                }
                Err(EEXIST())
            }
            Entry::Vacant(v) => {
                v.insert(Arc::new(RwLock::new(Dirent {
                    mode: mode,
                    file: None,
                    parent: Arc::downgrade(&fs),
                    children: Some(HashMap::new()),
                })));
                Ok(())
            }
        }
    }

    fn mkdir<P: AsRef<Path>>(&self, path: P, mode: u32) -> Result<()> {
        self.create_dir(path, mode, false)
    }

    fn create_dir_all<P: AsRef<Path>>(&self, path: P, mode: u32) -> Result<()> {
        let (_, parts) = self.up_path(path_parts::normalize(&path))?;
        let mut path_buf = PathBuf::new();
        for part in parts {
            path_buf.push(part.into_normal().unwrap());
            self.create_dir(&path_buf, mode, true)?;
        }
        Ok(())
    }

    // http://man7.org/linux/man-pages/man2/stat.2.html
    //
    // "No permissions are required on the file itself, but—in the case of stat() ... execute
    // (search) permission is required on all of the directories in pathname that lead to the file.
    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Metadata> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path))?;
        let fs = fs.read();
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(path) {
                    return Err(ENOENT());
                } else {
                    return Ok(Metadata {
                        filetype: FileType { dir: true },
                        perms: Permissions::from_mode(fs.mode),
                        length: DIRLEN,
                    });
                }
            }
        };

        if !fs.executable() {
            return Err(EACCES());
        }

        match fs.children.as_ref().unwrap().get(&base) {
            Some(child) => {
                let child = child.read();
                Ok(|| -> Metadata {
                    if child.is_dir() {
                        Metadata {
                            filetype: FileType { dir: true },
                            perms: Permissions::from_mode(child.mode),
                            length: DIRLEN,
                        }
                    } else {
                        Metadata {
                            filetype: FileType { dir: false },
                            perms: Permissions::from_mode(child.mode),
                            length: child.file.as_ref().unwrap().read().data.len() as u64,
                        }
                    }
                }())
            }
            None => Err(ENOENT()),
        }

    }

    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<ReadDir> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path))?;
        let fs = fs.read();
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else {
                    return ReadDir::new(&path, &*fs);
                }
            }
        };

        match fs.children.as_ref().unwrap().get(&base) {
            Some(child) => ReadDir::new(&path, &*child.read()),
            None => Err(ENOENT()),
        }
    }

    fn remove<P: AsRef<Path>>(&self, path: P, kind: FileType) -> Result<()> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path))?;
        let base = may_base.ok_or_else(|| if path_empty(&path) {
                               ENOENT()
                           } else {
                               EACCES()
                           })?;

        if !fs.read().executable() || !fs.read().writable() {
            return Err(EACCES());
        }

        // We need to make sure that the FileType being requested for removal matches the FileType
        // of the directory. Scope this check to let the non mutable borrow drop before removing.
        {
            let child = fs.read();
            let child = child.children.as_ref().unwrap().get(&base).ok_or_else(ENOENT)?;

            if kind.is_file() {
                if child.read().is_dir() {
                    return Err(EISDIR());
                }
            } else {
                if !child.read().is_dir() {
                    return Err(ENOTDIR());
                }
                if !child.read().children.as_ref().unwrap().is_empty() {
                    return Err(ENOTEMPTY());
                }
            }
        }

        fs.write().children.as_mut().unwrap().remove(&base);
        Ok(())
    }
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.remove(path, FileType { dir: false })
    }
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.remove(path, FileType { dir: true })
    }

    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        // Rust's remove_dir_all is actually very weak (weaker than rm -r). Rust relies on
        // read_dir to recurse, which requires `ls`. Standard linux is able to remove empty
        // directories with only write and execute privileges. This code attempts to mimic what
        // Rust will do.
        fn recursive_remove(fs: Arc<RwLock<Dirent>>) -> Result<()> {
            if fs.read().children.is_some() {
                let mut borrow = fs.write();
                if !borrow.readable() || !borrow.executable() || !borrow.writable() {
                    return Err(EACCES());
                }

                let mut children = borrow.children.as_mut().unwrap();
                let mut deleted = Vec::new();
                let res: Result<()> = {
                    let mut child_names = Vec::new();
                    for child in children.iter() {
                        child_names.push(child);
                    }
                    child_names.sort_by_key(|&(k, _)| k);

                    for &(child_name, child) in &child_names {
                        match recursive_remove(child.clone()) {
                            Ok(_) => {
                                deleted.push(child_name.clone());
                            }
                            Err(e) => {
                                return Err(e);
                            }
                        }
                    }
                    Ok(())
                };
                for child_name in deleted {
                    children.remove(&child_name);
                }
                res?
            } else {
                fs.write().file.as_mut().map(|f| f.write().invalidate());
            }
            Ok(())
        }

        let (fs, may_base) = self.traverse(path_parts::normalize(&path))?;
        let child = match may_base {
            Some(ref base) => {
                let fs = fs.read();
                if !fs.executable() || !fs.writable() {
                    return Err(EACCES());
                }
                match fs.children.as_ref().unwrap().get(base) {
                    Some(child) => child.clone(),
                    None => return Ok(()),
                }
            }
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else {
                    fs.clone()
                }
            }
        };

        recursive_remove(child)?;

        if let Some(ref base) = may_base {
            fs.write().children.as_mut().unwrap().remove(base);
        }
        Ok(())
    }

    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        let (old_fs, old_may_base) = self.traverse(path_parts::normalize(&from))?;
        let old_base = old_may_base.ok_or_else(|| if path_empty(&from) {
                                       ENOENT()
                                   } else {
                                       Error::new(ErrorKind::Other, "rename of root unimplemented")
                                   })?;
        let (new_fs, new_may_base) = self.traverse(path_parts::normalize(&to))?;
        let new_base =
            new_may_base.ok_or_else(|| if path_empty(&to) { ENOENT() } else { EEXIST() })?;

        if Arc::ptr_eq(&old_fs, &new_fs) && old_base == new_base {
            return Ok(());
        }

        if !old_fs.read().executable() || !old_fs.read().writable() {
            return Err(EACCES());
        }
        if !new_fs.read().executable() || !new_fs.read().writable() {
            return Err(EACCES());
        }

        // Rust's rename is strong, but also annoying, in that it can rename a directory to a
        // directory if that directory is empty. We could make the code elegant, but this will do.
        let (old_exist, old_is_dir) =
            match old_fs.read().children.as_ref().unwrap().get(&old_base) {
                Some(child) => (true, child.read().is_dir()),
                None => (false, false),
            };

        let (new_exist, new_is_dir, new_is_empty) =
            match new_fs.read().children.as_ref().unwrap().get(&new_base) {
                Some(child) => {
                    match child.read().children {
                        Some(ref children) => (true, true, children.is_empty()),
                        None => (true, false, false),
                    }
                }
                None => (false, false, false),
            };

        if !old_exist {
            return Err(ENOENT());
        }

        if !old_is_dir {
            if new_is_dir {
                return Err(EISDIR());
            }
        } else if new_exist {
            if new_is_dir {
                if !new_is_empty {
                    return Err(ENOTEMPTY());
                }
            } else {
                return Err(EEXIST());
            }
        }

        let removed = old_fs.write().children.as_mut().unwrap().remove(&old_base).unwrap();
        new_fs.write().children.as_mut().unwrap().insert(new_base, removed);
        Ok(())
    }

    fn open<P: AsRef<Path>>(&self, path: P, options: &OpenOptions) -> Result<File> {
        // We have create, create_new, read, write, truncate, append.
        //   - append implies write
        //   - create_new (excl) implies create
        //   - if !write, read is incompatible with any of create, create_new, and trunc
        //   - trunc and append are incompatible
        // First, let us validate the combinations and set implied fields.
        let mut options = options.clone();
        if options.append {
            options.write = true;
        }
        if options.excl {
            options.create = true;
        }
        if (options.create || options.trunc) && !options.write {
            return Err(EINVAL());
        }
        if options.trunc && options.append {
            return Err(EINVAL());
        }

        // Now we get on with opening.
        let (fs, may_base) = self.traverse(path_parts::normalize(&path))?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else {
                    return open_existing(&fs, &options);
                }
            }
        };
        if !fs.read().executable() {
            return Err(EACCES());
        }
        if let Some(child) = fs.read().children.as_ref().unwrap().get(&base) {
            return open_existing(child, &options);
        }

        // From here down, we worry about creating a new file.
        if !fs.read().writable() {
            return Err(EACCES());
        }
        if !options.create {
            return Err(ENOENT());
        }
        let file = Arc::new(RwLock::new(RawFile {
            valid: true,
            data: Vec::new(),
        }));
        let child = Arc::new(RwLock::new(Dirent {
            mode: options.mode,
            file: Some(file.clone()),
            parent: Arc::downgrade(&fs),
            children: None,
        }));
        fs.write().children.as_mut().unwrap().insert(base, child);
        Ok(File {
            read: options.read,
            write: options.write,
            append: options.append,
            metadata: Metadata {
                filetype: FileType { dir: false },
                length: 0,
                perms: Permissions::from_mode(options.mode),
            },
            file: file.clone(),
            at: 0,
        })
    }
}

// `open_existing` opens known existing file with the given options, returning an error if the file
// cannot be opened with those options.
fn open_existing(fs: &Arc<RwLock<Dirent>>, options: &OpenOptions) -> Result<File> {
    if options.excl {
        return Err(EEXIST());
    }

    let fs = fs.read();
    if fs.is_dir() {
        if options.write {
            return Err(EISDIR());
        }
        // TODO we could return Ok here so that users can stat the file, but that is more
        // complicated than seems worth it. Reads fail with "Is a directory", and right now
        // there is no hook into RawFile with how to fail reads.
        return Err(Error::new(ErrorKind::Other, "open on directory unimplemented"));
    }

    let (mut read, mut write) = (false, false);
    if options.read {
        if !fs.readable() {
            return Err(EACCES());
        }
        read = true;
    }
    if options.write {
        if !fs.writable() {
            return Err(EACCES());
        }
        write = true;
    }
    let (file, len) = {
        let arc_file = fs.file.as_ref().unwrap().clone();
        let len = {
            let mut raw_file = arc_file.write();
            if options.trunc {
                raw_file.data = Vec::new();
            }
            raw_file.data.len()
        };
        (arc_file, len)
    };
    Ok(File {
        read: read,
        write: write,
        append: options.append,
        metadata: Metadata {
            filetype: FileType { dir: false },
            length: len as u64,
            perms: Permissions::from_mode(options.mode),
        },
        file: file,
        at: 0,
    })
}

#[cfg(test)]
mod test {
    use super::*;
    use fs::{DirBuilder, DirEntry as DirEntryTrait, File, GenFS, OpenOptions};
    use std::ffi::OsString;
    use std::io::Error;
    use std::sync::mpsc;
    use std::thread;
    use unix_ext::*;

    fn errs_eq(l: Error, r: Error) -> bool {
        l.raw_os_error() == r.raw_os_error()
    }
    fn ref_errs_eq(l: &Error, r: &Error) -> bool {
        l.raw_os_error() == r.raw_os_error()
    }

    #[test]
    fn equal() {
        let exp_pwd = Arc::new(RwLock::new(Dirent {
            mode: 0o0,
            file: None,
            parent: Weak::new(),
            children: Some(HashMap::new()),
        }));

        let exp = FS {
            inner: Arc::new(Mutex::new(FileSystem {
                root: exp_pwd.clone(),
                pwd: exp_pwd,
            })),
        };
        {
            let ref mut root = exp.inner.lock().pwd;
            root.write()
                .children
                .as_mut()
                .unwrap()
                .insert(OsString::from("lolz"),
                        Arc::new(RwLock::new(Dirent {
                            mode: 0o666,
                            file: None,
                            parent: Arc::downgrade(&root),
                            children: Some(HashMap::new()),
                        })));
        }

        let fs = FS::with_mode(0o777);
        assert!(fs.new_dirbuilder().mode(0o666).create("lolz").is_ok());
        assert!(fs.set_permissions("/", Permissions::from_mode(0)).is_ok());
        assert!(fs == exp);
    }

    #[test]
    fn mkdir() {
        let exp_pwd = Arc::new(RwLock::new(Dirent {
            mode: 0o300,
            file: None,
            parent: Weak::new(),
            children: Some(HashMap::new()),
        }));
        let exp = FS {
            inner: Arc::new(Mutex::new(FileSystem {
                root: exp_pwd.clone(),
                pwd: exp_pwd,
            })),
        };

        {
            let ref mut root = exp.inner.lock().pwd;
            let mut borrow = root.write();
            let children = borrow.children.as_mut().unwrap();
            children.insert(OsString::from("a"),
                            Arc::new(RwLock::new(Dirent {
                                mode: 0o500, // r-x: cannot create subfiles
                                file: None,
                                parent: Arc::downgrade(&root),
                                children: Some(HashMap::new()),
                            })));
            children.insert(OsString::from("b"),
                            Arc::new(RwLock::new(Dirent {
                                mode: 0o600, // rw-: cannot exec (cd) into to create subfiles
                                file: None,
                                parent: Arc::downgrade(&root),
                                children: Some(HashMap::new()),
                            })));
            let child = Arc::new(RwLock::new(Dirent {
                mode: 0o300, // _wx: all we need
                file: None,
                parent: Arc::downgrade(&root),
                children: Some(HashMap::new()),
            }));
            {
                let mut child_borrow = child.write();
                let child_children = child_borrow.children.as_mut().unwrap();
                child_children.insert(OsString::from("d"),
                                      Arc::new(RwLock::new(Dirent {
                                          mode: 0o777,
                                          file: None,
                                          parent: Arc::downgrade(&child),
                                          children: Some(HashMap::new()),
                                      })));
            }
            children.insert(OsString::from("c"), child);

        }

        // fs
        // ├-a/
        // ├-b/
        // └-c/
        //   └-d/
        let fs = FS::with_mode(0o300);
        assert!(fs.new_dirbuilder().mode(0o500).create("/../a").is_ok());
        assert!(fs.new_dirbuilder().mode(0o600).create("../b").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).create("c").is_ok());
        assert!(fs.cd("c").is_ok());
        assert!(fs.new_dirbuilder().mode(0o777).create("d").is_ok());
        assert!(fs == exp);
        assert!(fs.cd("..").is_ok());
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("a/z").unwrap_err(),
                        EACCES()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("b/z").unwrap_err(),
                        EACCES()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("").unwrap_err(),
                        ENOENT()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("/").unwrap_err(),
                        EEXIST()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("a").unwrap_err(),
                        EEXIST()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("z/z").unwrap_err(),
                        ENOENT()));
    }

    #[test]
    fn create_dir_all() {
        let fs = FS::with_mode(0o300);
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("////").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("a/b/c").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("/a/b/c/").is_ok());
        assert!(errs_eq(fs.new_dirbuilder()
                          .mode(0o100)
                          .recursive(true)
                          .create("d/e/f")
                          .unwrap_err(),
                        EACCES()));

        let exp = FS::with_mode(0o300);
        assert!(exp.new_dirbuilder().mode(0o300).create("a").is_ok());
        assert!(exp.new_dirbuilder().mode(0o300).create("a/b").is_ok());
        assert!(exp.new_dirbuilder().mode(0o300).create("a/b/c").is_ok());
        assert!(exp.new_dirbuilder().mode(0o100).create("d").is_ok());
        assert!(fs == exp);

        assert!(fs.cd("a/b/c").is_ok());
        assert!(fs.set_permissions("..", Permissions::from_mode(0o600)).is_ok());
        assert!(errs_eq(fs.new_dirbuilder().mode(0o100).create("../../z").unwrap_err(),
                        EACCES()));
        assert!(errs_eq(fs.new_dirbuilder()
                          .mode(0o100)
                          .recursive(true)
                          .create("../../z")
                          .unwrap_err(),
                        EACCES()));
        assert!(exp.set_permissions("a/b", Permissions::from_mode(0o600)).is_ok());
        assert!(fs == exp);
    }

    #[test]
    fn open() {
        let fs = FS::with_mode(0o700);
        let exp = FS::with_mode(0o700);
        {
            let ref mut root = exp.inner.lock().pwd;
            root.write()
                .children
                .as_mut()
                .unwrap()
                .insert(OsString::from("a"),
                        Arc::new(RwLock::new(Dirent {
                            mode: 0o300,
                            file: Some(Arc::new(RwLock::new(RawFile {
                                valid: true,
                                data: vec![1, 2, 3, 4],
                            }))),
                            parent: Arc::downgrade(&root),
                            children: None,
                        })));
        }
        let mut file = fs.new_openopts().create(true).write(true).mode(0o300).open("a").unwrap();
        assert!(file.write(vec![1, 2, 3, 4].as_slice()).is_ok());

        assert!(fs.new_dirbuilder().mode(0o100).create("unwrite").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("unexec/subdir").is_ok());
        assert!(fs.set_permissions("unexec", Permissions::from_mode(0o200)).is_ok());

        assert!(errs_eq(fs.new_openopts().write(true).open("").unwrap_err(),
                        ENOENT()));

        fn test_open<P: AsRef<Path>>(on: i32,
                                     fs: &FS,
                                     read: bool,
                                     write: bool,
                                     append: bool,
                                     trunc: bool,
                                     excl: bool,
                                     create: bool,
                                     mode: u32,
                                     path: P,
                                     err: Option<Error>) {
            let res = fs.new_openopts()
                        .read(read)
                        .write(write)
                        .append(append)
                        .truncate(trunc)
                        .create_new(excl)
                        .create(create)
                        .mode(mode)
                        .open(&path);

            if err.is_some() {
                if res.is_ok() {
                    panic!("#{}: expected an error", on);
                }
                let (res_err, exp_err) = (res.unwrap_err(), err.unwrap());
                if res_err.kind() == ErrorKind::Other && exp_err.kind() == ErrorKind::Other {
                    return;
                }
                assert!(ref_errs_eq(&res_err, &exp_err),
                        "#{}: got err {:?} != exp err {:?}",
                        on,
                        &res_err,
                        &exp_err);
                return;
            }

            if res.is_err() {
                panic!("#{}: not ok: {:?}", on, res.unwrap_err());
            }
            let file = res.unwrap();
            assert!(read == file.read);
            assert!((write || append) == file.write);
            assert!(append == file.append);
            assert!(file.metadata().unwrap().is_file());
        }

        let (t, f) = (true, false);
        let mut i = -1;
        let mut on = || -> i32 {
            i += 1;
            i
        };
        //                   r, w, a, t, e, c
        // No ent...
        test_open(on(), &fs, t, t, t, f, t, t, 0o700, "", Some(ENOENT()));
        // Bad perm combos...
        test_open(on(), &fs, t, f, f, t, f, f, 0o700, "/", Some(EINVAL())); // r t
        test_open(on(), &fs, t, f, f, f, t, f, 0o700, "/", Some(EINVAL())); // r e
        test_open(on(), &fs, t, f, f, f, f, t, 0o700, "/", Some(EINVAL())); // r c
        test_open(on(), &fs, f, t, t, t, f, f, 0o700, "/", Some(EINVAL())); // w a t

        // Open on a directory with write is bad...
        test_open(on(), &fs, f, t, f, f, f, f, 0o700, "/", Some(EISDIR())); // w

        // Open on a directory is invalid in this code.
        test_open(on(),
                  &fs,
                  t,
                  f,
                  f,
                  f,
                  f,
                  f,
                  0o700,
                  "/",
                  Some(Error::new(ErrorKind::Other, "")));

        // New files in unreachable directories...
        test_open(on(),
                  &fs,
                  f,
                  t,
                  f,
                  f,
                  t,
                  f,
                  0o200,
                  "unexec/a",
                  Some(EACCES()));
        test_open(on(),
                  &fs,
                  f,
                  t,
                  f,
                  f,
                  t,
                  f,
                  0o200,
                  "unwrite/a",
                  Some(EACCES()));

        // New files...
        test_open(on(), &fs, t, f, f, f, f, f, 0o700, "f", Some(ENOENT())); // r
        test_open(on(), &fs, f, t, f, f, t, f, 0o700, "f", None); // w e
        test_open(on(), &fs, f, t, f, f, t, f, 0o300, "f", Some(EEXIST())); // w e
        test_open(on(), &fs, f, t, f, f, t, f, 0o200, "/", Some(EEXIST())); // w e

        // New files, valid flags.
        test_open(on(), &fs, t, f, f, f, f, f, 0o300, "f", None); // r
        test_open(on(), &fs, t, f, t, f, f, f, 0o300, "f", None); // r a
        test_open(on(), &fs, t, f, t, f, f, t, 0o300, "f", None); // r a c
        test_open(on(), &fs, t, f, t, f, t, f, 0o700, "g", None); // r a e
        test_open(on(), &fs, t, f, t, f, f, t, 0o300, "h", None); // r a e c
        test_open(on(), &fs, t, t, t, f, f, t, 0o300, "g", None); // r w a c
        test_open(on(), &fs, t, t, f, t, t, t, 0o700, "i", None); // r w t e c
        test_open(on(), &fs, t, t, t, f, f, t, 0o300, "i", None); // r w a c
        test_open(on(), &fs, f, t, f, f, f, t, 0o300, "i", None); // w c

        // New files, strict perms on creation, attempt reopen with bad flags.
        test_open(on(), &fs, t, t, f, f, f, t, 0o300, "f_unread", None); // r
        test_open(on(),
                  &fs,
                  t,
                  t,
                  f,
                  f,
                  f,
                  t,
                  0o300,
                  "f_unread",
                  Some(EACCES()));
        test_open(on(), &fs, f, t, f, f, f, t, 0o500, "f_unwrite", None); // w
        test_open(on(),
                  &fs,
                  f,
                  t,
                  f,
                  f,
                  f,
                  t,
                  0o500,
                  "f_unwrite",
                  Some(EACCES()));
    }

    #[test]
    fn remove() {
        let fs = FS::with_mode(0o700);
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("unexec/subdir/d").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("a/d/e").is_ok());
        assert!(fs.new_dirbuilder().mode(0o000).create("a/b").is_ok());
        assert!(fs.new_openopts().write(true).create(true).mode(0o400).open("a/c").is_ok());
        assert!(fs.set_permissions("unexec", Permissions::from_mode(0o200)).is_ok());

        // ├--a/
        // |  ├--b/
        // |  ├--c
        // |  └--d/
        // |     └--e/
        // └--unexecable/
        //     └--subdir/
        //         └--d/

        // While we are here, quickly test that mkdir on an existing file fails - we did not test
        // above in mkdir as we were, at the time, proving mkdir worked exactly.
        assert!(errs_eq(fs.new_dirbuilder().mode(0o300).create("a/c").unwrap_err(),
                        EEXIST()));

        assert!(errs_eq(fs.remove_dir("").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.remove_dir("/").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.remove_dir("unexec/subdir").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.remove_dir("unexec/subdir/d").unwrap_err(), EACCES()));

        assert!(errs_eq(fs.remove_dir("a/c/z").unwrap_err(), ENOTDIR()));
        assert!(errs_eq(fs.remove_dir("a/z").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.remove_dir("a/d").unwrap_err(), ENOTEMPTY()));

        assert!(fs.cd("a/d").is_ok()); // cd and do some relative removes

        assert!(fs.remove_file("../c").is_ok());
        assert!(errs_eq(fs.remove_dir("../../unexec/subdir").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.remove_dir("../d").unwrap_err(), ENOTEMPTY()));
        assert!(fs.remove_dir("../d/e/./").is_ok());

        assert!(fs.cd("../..").is_ok()); // cd back to not lose ourself

        assert!(fs.remove_dir("a/d").is_ok());
        assert!(errs_eq(fs.remove_dir("a/d").unwrap_err(), ENOENT()));
    }

    #[test]
    fn remove_dir_all() {
        let fs = FS::with_mode(0o700);
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("j/k/l").is_ok());
        assert!(fs.new_openopts().mode(0o000).write(true).create(true).open("j/f").is_ok());
        assert!(fs.new_dirbuilder().mode(0o500).create("x").is_ok());

        // ├--a/
        // |  └--b/
        // |     └--c/
        // ├--j/
        // |  ├--f
        // |  └--k/
        // |     └--l/
        // └--x/

        assert!(errs_eq(fs.remove_dir_all("").unwrap_err(), ENOENT()));
        assert!(fs.remove_dir_all("a").is_ok());
        assert!(fs.remove_dir_all("j").is_ok());
        assert!(errs_eq(fs.remove_dir_all("x").unwrap_err(), EACCES()));

        let exp = FS::with_mode(0o700);
        assert!(exp.new_dirbuilder().mode(0o500).create("x").is_ok());
        assert!(fs == exp);
    }

    #[test]
    fn rename() {
        let fs = FS::with_mode(0o700);
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("d/e").is_ok());
        assert!(fs.set_permissions("a/b", Permissions::from_mode(0o600)).is_ok()); // cannot exec
        assert!(fs.new_openopts().mode(0).write(true).create(true).open("f").is_ok());
        assert!(fs.new_openopts().mode(0).write(true).create(true).open("g").is_ok());

        assert!(errs_eq(fs.rename("a/b/c/d", "").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.rename("a", "a/b/c/d").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.rename("", "d/e/f").unwrap_err(), ENOENT()));
        assert!(fs.rename("/", "d/e/f").unwrap_err().kind() == ErrorKind::Other);
        assert!(errs_eq(fs.rename("a/b/c", "").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.rename("d", "/").unwrap_err(), EEXIST()));
        assert!(fs.rename("a", "a").is_ok());
        assert!(errs_eq(fs.rename("a/b/c", "d").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.rename("d", "a/b/d").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.rename("a/z", "d/z").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.rename("a", "d").unwrap_err(), ENOTEMPTY()));
        assert!(errs_eq(fs.rename("a", "f").unwrap_err(), EEXIST()));
        assert!(errs_eq(fs.rename("f", "a").unwrap_err(), EISDIR()));
        assert!(fs.rename("a", "d/a").is_ok());
        assert!(fs.rename("d/a", "d/e").is_ok());
        assert!(fs.rename("f", "z").is_ok());
        assert!(fs.rename("g", "z").is_ok());

        let exp = FS::with_mode(0o700);
        assert!(exp.new_dirbuilder().mode(0o700).recursive(true).create("d/e/b/c").is_ok());
        assert!(exp.set_permissions("d/e/b", Permissions::from_mode(0o600)).is_ok());
        assert!(exp.new_openopts().mode(0).write(true).create(true).open("z").is_ok());
        assert!(fs == exp);
    }

    #[test]
    fn read_dir() {
        let fs = FS::with_mode(0o700);
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).create("a/b/d").is_ok());
        assert!(fs.new_dirbuilder().mode(0o100).create("a/b/z").is_ok());
        assert!(fs.new_openopts().mode(0o000).write(true).create(true).open("a/b/f").is_ok());

        let mut reader = fs.read_dir("a/b").unwrap();
        assert_eq!(reader.next().unwrap().unwrap(),
                   DirEntry {
                       dir: PathBuf::from("a/b"),
                       base: OsString::from("c"),
                       meta: Metadata {
                           filetype: FileType { dir: true },
                           length: DIRLEN,
                           perms: Permissions::from_mode(0o700),
                       },
                   });
        assert_eq!(reader.next().unwrap().unwrap(),
                   DirEntry {
                       dir: PathBuf::from("a/b"),
                       base: OsString::from("d"),
                       meta: Metadata {
                           filetype: FileType { dir: true },
                           length: DIRLEN,
                           perms: Permissions::from_mode(0o300),
                       },
                   });
        let next = reader.next().unwrap().unwrap();
        assert_eq!(next.path(), PathBuf::from("a/b/f"));
        assert_eq!(next.file_name(), OsString::from("f"));
        assert_eq!(next.metadata().unwrap(),
                   Metadata {
                       filetype: FileType { dir: false },
                       length: 0,
                       perms: Permissions::from_mode(0),
                   });
        let next = reader.next().unwrap().unwrap();
        assert_eq!(next.path(), PathBuf::from("a/b/z"));
        assert_eq!(next.file_name(), OsString::from("z"));
        assert_eq!(next.metadata().unwrap(),
                   Metadata {
                       filetype: FileType { dir: true },
                       length: DIRLEN,
                       perms: Permissions::from_mode(0o100),
                   });
        assert!(reader.next().is_none());
    }

    #[test]
    fn raw_file() {
        let mut raw_file = RawFile {
            valid: true,
            data: Vec::new(),
        };

        let slice = &[1, 2, 3, 4, 5];
        assert_eq!(raw_file.write_at(0, &slice[..3]).unwrap(), 3);
        assert_eq!(raw_file.data.as_slice(), &[1, 2, 3]);

        let mut output = [0u8; 5];
        assert_eq!(raw_file.read_at(0, &mut output).unwrap(), 3);
        assert_eq!(&output, &[1, 2, 3, 0, 0]);

        assert_eq!(raw_file.read_at(1, &mut output).unwrap(), 2);
        assert_eq!(&output, &[2, 3, 3, 0, 0]);

        assert_eq!(raw_file.read_at(2, &mut output).unwrap(), 1);
        assert_eq!(&output, &[3, 3, 3, 0, 0]);

        assert_eq!(raw_file.read_at(3, &mut output).unwrap(), 0);
        assert_eq!(&output, &[3, 3, 3, 0, 0]);

        assert_eq!(raw_file.write_at(1, &slice[..4]).unwrap(), 4);
        assert_eq!(raw_file.data.as_slice(), &[1, 1, 2, 3, 4]);

        assert_eq!(raw_file.write_at(1, slice).unwrap(), 5);
        assert_eq!(raw_file.data.as_slice(), &[1, 1, 2, 3, 4, 5]);

        assert_eq!(raw_file.read_at(1, &mut output).unwrap(), 5);
        assert_eq!(&output, &[1, 2, 3, 4, 5]);

        assert_eq!(raw_file.read_at(0, &mut output).unwrap(), 5);
        assert_eq!(&output, &[1, 1, 2, 3, 4]);

        assert_eq!(raw_file.valid, true);
        raw_file.invalidate();
        assert_eq!(raw_file.valid, false);
        assert!(errs_eq(raw_file.write_at(0, slice).unwrap_err(), ENOENT()));
        assert!(errs_eq(raw_file.read_at(0, &mut output).unwrap_err(), ENOENT()));
    }

    // This test duplicates the example at the top, but is down here for code coverage purposes and
    // also just in case the example changes. This additionally adds some seeking and repeated
    // read/writes to test those functions...
    #[test]
    fn test_usage() {
        let fs = FS::with_mode(0o300);
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());

        let mut wf =
            fs.new_openopts().mode(0o600).write(true).create_new(true).open("a/f").unwrap();
        assert_eq!(wf.write(vec![0, 1, 2, 3, 4, 5].as_slice()).unwrap(), 6);
        assert_eq!(wf.seek(SeekFrom::Start(1)).unwrap(), 1);
        assert_eq!(wf.write(vec![1, 2, 3].as_slice()).unwrap(), 3);

        let mut rf = fs.new_openopts().read(true).open("a/f").unwrap();
        assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);

        let mut output = [0u8; 4];
        assert_eq!(rf.read(&mut output).unwrap(), 4);
        assert_eq!(&output, &[1, 2, 3, 4]);
        assert_eq!(rf.seek(SeekFrom::Start(2)).unwrap(), 2);
        assert_eq!(rf.read(&mut output).unwrap(), 4);
        assert_eq!(&output, &[2, 3, 4, 5]);

        let mut reader = fs.read_dir("a").unwrap();

        let next = reader.next().unwrap().unwrap();
        assert_eq!(next.file_name(), OsString::from("b"));
        assert_eq!(next.path(), PathBuf::from("a/b"));

        let next = reader.next().unwrap().unwrap();
        assert_eq!(next.file_name(), OsString::from("f"));
        assert_eq!(next.path(), PathBuf::from("a/f"));

        assert!(reader.next().is_none());
    }

    #[test]
    fn test_thread() {
        let fs = FS::with_mode(0o300);
        let (tx, rx) = mpsc::channel();
        {
            let fs = fs.clone();
            thread::spawn(move || {
                assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());
                tx.send(()).unwrap();
            });
        }
        rx.recv().unwrap();
        assert!(fs.metadata("a/b/c").is_ok());
    }
}
