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

use self::parking_lot::{Mutex, RwLock};

use std::cmp::{self, Ordering};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ffi::OsString;
use std::io::{Error, ErrorKind, Read, Result, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Weak};
use std::vec::IntoIter;

use fs::{self, FileType as _FileType, Metadata as _Metadata};
use unix_ext::{self, PermissionsExt as _PermissionsExt};

use errors::*;
use path_parts::{self, IteratorExt, Part};

// TODO File could be tested more, maybe, but the raw_file seems sufficient.
// Permissions and FileType can be tested directly - right now they are tested indirectly.

// DIRLEN is the length returned from Metadata's len() call for a directory. This is pulled from
// the initial file size that Unix uses for a directory sector. This module does not attempt to
// return a larger number if the directory contains many children with long names.
const DIRLEN: u64 = 4096;
const SYMLEN: u64 = 1;

/// A builder used to create directories in various manners.
///
/// See the module [documentation] for a comprehensive example.
///
/// [documentation]: index.html
#[derive(Debug)]
pub struct DirBuilder {
    fs: FS,

    recursive: bool,
    mode:      u32,
}

impl fs::DirBuilder for DirBuilder {
    fn recursive(&mut self, recursive: bool) -> &mut Self {
        self.recursive = recursive; self
    }
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        if self.recursive {
            self.fs.inner.lock().create_dir_all(path, self.mode)
        } else {
            self.fs.inner.lock().create_dir(path, self.mode, false)
        }
    }
}

impl unix_ext::DirBuilderExt for DirBuilder {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.mode = mode; self
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
    dir:  PathBuf,
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
    data:  Vec<u8>,
}

impl RawFile {
    // read_at reads contents of the file into dst from a given existing index in the file.
    fn read_at(&self, at: usize, dst: &mut [u8]) -> Result<usize> {
        if !self.valid {
            return Err(ENOENT());
        }

        let data = &self.data;
        if at > data.len() {
            return Ok(0);
        }

        let unread = &data[at..];
        let copy_size = cmp::min(dst.len(), unread.len());

        dst[..copy_size].copy_from_slice(&unread[..copy_size]);
        Ok(copy_size)
    }

    // write_at writes to the RawFile at a given index.
    fn write_at(&mut self, at: usize, src: &[u8]) -> Result<usize> {
        if !self.valid {
            return Err(ENOENT());
        }

        let mut dst = &mut self.data;

        if at > dst.len() {
            let new = vec![0; at + src.len()];
            *dst = new;
        }

        let new_end = src.len() + at;

        if dst.len() >= new_end {
            dst[at..new_end].copy_from_slice(src);
        } else {
            dst.truncate(at);
            dst.extend_from_slice(src);
        }
        Ok(src.len())
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
#[derive(Clone, Debug)]
pub struct File {
    // fields that allow us to set_permissions...
    fs:   FS,
    path: PathBuf,

    read:   bool,
    write:  bool,
    append: bool,

    metadata: Metadata,

    cursor: Arc<Mutex<FileCursor>>,
}

// FileCursor corresponds to an actual file descriptor, which, "behind the scenes", keeps track of
// where we are in a file.
#[derive(Debug)]
struct FileCursor {
    file: Arc<RwLock<RawFile>>,
    at:   usize,
}

impl fs::File for File {
    type Metadata    = Metadata;
    type Permissions = Permissions;

    fn sync_all(&self) -> Result<()> {
        Ok(())
    }
    fn sync_data(&self) -> Result<()> {
        Ok(())
    }
    fn set_len(&self, size: u64) -> Result<()> {
        if !self.write {
            return Err(EINVAL());
        }
        Ok(self.cursor.lock().set_len(size)?)
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        Ok(self.metadata)
    }
    fn try_clone(&self) -> Result<Self> {
        Ok(self.clone())
    }
    fn set_permissions(&self, perm: Self::Permissions) -> Result<()> {
        use fs::GenFS;
        Ok(self.fs.set_permissions(&self.path, perm)?)
    }
}

impl FileCursor {
    fn set_len(&mut self, size: u64) -> Result<()> {
        let mut file = self.file.write();
        let size = size as usize;
        match file.data.len().cmp(&size) {
            Ordering::Less => {
                // If data is smaller, create a longer Vec and copy the original contents over.
                let mut new = vec![0; size];
                new[..file.data.len()].copy_from_slice(&file.data);
                file.data = new;
            }
            // If data is longer, simply truncate it.
            Ordering::Greater => file.data.truncate(size),
            // Truncate to the length data is? Do nothing!
            _ => (),
        }
        Ok(())
    }

    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let n = self.file.read().read_at(self.at, buf)?;
        self.at += n;
        Ok(n)
    }

    fn write(&mut self, buf: &[u8], append: bool) -> Result<usize> {
        let mut file = self.file.write();
        if append {
            self.at = file.data.len();
        }
        let n = file.write_at(self.at, buf)?;
        self.at += n;
        Ok(n)
    }

    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        let file = self.file.write();
        let len = file.data.len();
        // seek seemingly returns (if successful) the sum of the position we are seeking from and
        // the offset. This is the case even if we seek past the end of the file.
        match pos {
            SeekFrom::Start(offset) => {
                self.at = cmp::min(len, offset as usize);
                Ok(offset)
            }
            SeekFrom::Current(offset) => {
                let at_end = (self.at as i64).saturating_add(offset);
                if at_end < 0 {
                    return Err(EINVAL());
                }
                self.at = cmp::min(len, at_end as usize);
                Ok(at_end as u64)
            }
            SeekFrom::End(offset) => {
                let at_end = (len as i64).saturating_add(offset);
                if at_end < 0 {
                    return Err(EINVAL());
                }
                self.at = cmp::min(len, at_end as usize);
                Ok(at_end as u64)
            }
        }
    }
}

impl Read for File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        if !self.read {
            return Err(EBADF());
        }
        Ok(self.cursor.lock().read(buf)?)
    }
}
impl Write for File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        if !self.write {
            return Err(EBADF());
        }
        Ok(self.cursor.lock().write(buf, self.append)?)
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
        Ok(self.cursor.lock().seek(pos)?)
    }
}

// now we duplicate our impls for a &'a File - this is necessary because we can call mutable
// functions (read, write, flush, seek) on a file reference.

impl<'a> Read for &'a File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        if !self.read {
            return Err(EBADF());
        }
        Ok(self.cursor.lock().read(buf)?)
    }
}
impl<'a> Write for &'a File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        if !self.write {
            return Err(EBADF());
        }
        Ok(self.cursor.lock().write(buf, self.append)?)
    }
    fn flush(&mut self) -> Result<()> {
        if !self.write {
            return Err(EBADF());
        }
        Ok(())
    }
}
impl<'a> Seek for &'a File {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        Ok(self.cursor.lock().seek(pos)?)
    }
}

impl unix_ext::FileExt for File {
    fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize> {
        if !self.read {
            return Err(EBADF());
        }
        let cursor = self.cursor.lock();
        let file = cursor.file.read();
        Ok(file.read_at(offset as usize, buf)?)
    }
    fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize> {
        if !self.write {
            return Err(EBADF());
        }
        let cursor = self.cursor.lock();
        let mut file = cursor.file.write();
        Ok(file.write_at(offset as usize, buf)?)
    }
}

// Ftyp is the actual underlying enum for a FileType.
#[derive(Copy, Clone, Debug, PartialEq)]
enum Ftyp {
    File,
    Dir,
    Symlink,
}

/// Represents the type of a file.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct FileType(Ftyp);

impl fs::FileType for FileType {
    fn is_dir(&self) -> bool {
        self.0 == Ftyp::Dir
    }
    fn is_file(&self) -> bool {
        self.0 == Ftyp::File
    }
    //fn is_symlink(&self) -> bool {
    //    self.0 == Ftyp::Symlink
    //}
}

/// Metadata information about a file.
///
/// See the module [documentation] for a comprehensive example.
///
/// [documentation]: index.html
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Metadata {
    filetype: FileType,
    length:   u64,
    perms:    Permissions,
}

impl fs::Metadata for Metadata {
    type Permissions = Permissions;
    type FileType    = FileType;

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
    fs:     FS,
    read:   bool,
    write:  bool,
    append: bool,
    trunc:  bool,
    create: bool,
    excl:   bool,
    mode:   u32,
}

impl fs::OpenOptions for OpenOptions {
    type File = File;

    fn read(&mut self, read: bool) -> &mut Self {
        self.read = read; self
    }
    fn write(&mut self, write: bool) -> &mut Self {
        self.write = write; self
    }
    fn append(&mut self, append: bool) -> &mut Self {
        self.append = append; self
    }
    fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.trunc = truncate; self
    }
    fn create(&mut self, create: bool) -> &mut Self {
        self.create = create; self
    }
    fn create_new(&mut self, create_new: bool) -> &mut Self {
        self.excl = create_new; self
    }
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        self.fs.inner.lock().open(self.fs.clone(), path, self, &mut 0)
    }
}

impl unix_ext::OpenOptionsExt for OpenOptions {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.mode = mode; self
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
    fn new<P: AsRef<Path>>(path: P, dir: &Dirent) -> Result<ReadDir> {
        if !dir.readable() {
            return Err(EACCES());
        }
        let children = {
            match dir.kind {
                DeKind::Dir(ref children) => children,
                _ => return Err(ENOTDIR()),
            }
        };

        // iterate over the children and create a bunch of DirEntrys as appropriate.
        let mut dirents = Vec::new();
        for (base, dirent) in children.iter() {
            let dirent = dirent.read();
            dirents.push(DirEntry {
                dir:  PathBuf::from(path.as_ref()),
                base: base.clone(),
                meta: match dirent.kind {
                    DeKind::Dir(_) => Metadata {
                        filetype: FileType(Ftyp::Dir),
                        length:   DIRLEN,
                        perms:    Permissions::from_mode(dirent.mode),
                    },
                    DeKind::File(ref f) => Metadata {
                        filetype: FileType(Ftyp::File),
                        length:   f.read().data.len() as u64,
                        perms:    Permissions::from_mode(dirent.mode),
                    },
                    DeKind::Symlink(_) => Metadata {
                        filetype: FileType(Ftyp::Symlink),
                        length:   SYMLEN,
                        perms:    Permissions::from_mode(dirent.mode),
                    },
                },
            });
        }
        // read_dir on every system I have ever used returns dirents in alphabetical order, so we
        // will recreate that behavior here.
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
            parent: Weak::new(),
            kind:   DeKind::Dir(HashMap::new()),
            mode:   mode,
        }));
        FS {
            inner: Arc::new(Mutex::new(FileSystem {
                root: pwd.clone(),
                pwd:  pwd,
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
        self.inner.lock().cd(path, &mut 0)
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
    type DirBuilder  = DirBuilder;
    type DirEntry    = DirEntry;
    type Metadata    = Metadata;
    type OpenOptions = OpenOptions;
    type Permissions = Permissions;
    type ReadDir     = ReadDir;

    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Metadata> {
        self.inner.lock().metadata(path)
    }
    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<ReadDir> {
        self.inner.lock().read_dir(path, &mut 0)
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
        self.inner.lock().set_permissions(path, perm.mode, &mut 0)
    }

    fn new_openopts(&self) -> OpenOptions {
        OpenOptions {
            fs:     self.clone(),
            read:   false,
            write:  false,
            append: false,
            trunc:  false,
            create: false,
            excl:   false,
            mode:   0o666, // default per unix_ext
        }
    }
    fn new_dirbuilder(&self) -> DirBuilder {
        DirBuilder {
            fs: self.clone(),

            recursive: false,
            mode:      0o777, // default per unix_ext
        }
    }
}

// DeKind differentiates between files, directories, and symlinks.
#[derive(Debug)]
enum DeKind {
    File(Arc<RwLock<RawFile>>),
    Dir(HashMap<OsString, Arc<RwLock<Dirent>>>),
    Symlink(PathBuf),
}

impl DeKind {
    fn file_ref(&self) -> &Arc<RwLock<RawFile>> {
        match *self {
            DeKind::File(ref f) => f,
            _ => panic!("file_ref used on DeKind when not a file"),
        }
    }
    fn dir_ref(&self) -> &HashMap<OsString, Arc<RwLock<Dirent>>> {
        match *self {
            DeKind::Dir(ref d) => d,
            _ => panic!("dir_ref used on DeKind when not a dir"),
        }
    }
    fn dir_mut(&mut self) -> &mut HashMap<OsString, Arc<RwLock<Dirent>>> {
        match *self {
            DeKind::Dir(ref mut d) => d,
            _ => panic!("dir_mut used on DeKind when not a dir"),
        }
    }
}

// Dirent represents all information needed at a node in our filesystem tree.
#[derive(Debug)]
struct Dirent {
    parent: Weak<RwLock<Dirent>>,
    kind:   DeKind,
    mode:   u32,
}

impl Dirent {
    fn is_dir(&self) -> bool {
        match self.kind {
            DeKind::Dir(_) => true,
            _ => false,
        }
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

// FileSystem is a single in-memory filesystem that can be cloned and passed around safely.
#[derive(Debug)]
struct FileSystem {
    root: Arc<RwLock<Dirent>>,
    pwd:  Arc<RwLock<Dirent>>,
}

fn path_empty<P: AsRef<Path>>(path: P) -> bool {
    path.as_ref() == Path::new("")
}

// We claim that two filesystems are equal if they have the same structure, contents, and modes.
impl PartialEq for FileSystem {
    fn eq(&self, other: &FileSystem) -> bool {
        fn eq_at(l: Arc<RwLock<Dirent>>, r: Arc<RwLock<Dirent>>) -> bool {
            let l = l.read();
            let r = r.read();
            if l.mode != r.mode {
                return false;
            }
            match (&l.kind, &r.kind) {
                (&DeKind::File(ref fl), &DeKind::File(ref fr)) => fl.read().data == fr.read().data,
                (&DeKind::Dir(ref dl), &DeKind::Dir(ref dr)) => {
                    if dl.len() != dr.len() {
                        return false;
                    }
                    for (child_name, cl) in dl.iter() {
                        match dr.get(child_name) {
                            Some(cr) => if !eq_at(cl.clone(), cr.clone()) {
                                return false;
                            },
                            None => return false,
                        }
                    }
					true
                },
                (&DeKind::Symlink(ref sl), &DeKind::Symlink(ref sr)) => sl == sr,
                _ => false,
            }
        }

        eq_at(self.root.clone(), other.root.clone())
    }
}

impl FileSystem {
    // up_path traverses up parent directories in a normalized path, erroring if we cannot cd into
    // (exec) the parent directory. This function does nothing with symlinks, meaning if the
    // filesystem is _inside_ of a symlink, functions with relative paths need handled somehow.
    fn up_path(&self,
               parts: path_parts::Parts)
               -> Result<(Arc<RwLock<Dirent>>, path_parts::Parts)> {
        // If (normalized) parts begins at root, there are no ParentDirs.
        if parts.at_root() {
            return Ok((self.root.clone(), parts));
        }

        // `up` is what we return: the dirent after traversing up all ParentDirs in `parts`.
        let mut up = self.pwd.clone();
        let mut parts_iter = parts.into_iter().peekable();
        while parts_iter.peek()
                        .and_then(|part| if *part == Part::ParentDir { Some(()) } else { None })
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
    //
    // This traverses all symlinks up to the base of the input path.
    fn traverse(&self,
                parts: path_parts::Parts,
                level: &mut u8)
                -> Result<(Arc<RwLock<Dirent>>, Option<OsString>)> {
        if {*level += 1; *level} == 40 {
            return Err(ELOOP());
        }
        // First, we eat the parent directories. What remains will be purely normal paths.
        let (mut fs, parts) = self.up_path(parts)?;
        let mut parts_iter = parts.into_iter().peek2able();
        // Until the base of the input path, we change down paths.
        while parts_iter.peek2().is_some() {
            if !fs.read().executable() {
                return Err(EACCES());
            }

            fs = {
                let borrow = fs.read();
                match borrow.kind {
                    // We are at a normal directory: change down into the child, if it exists.
                    DeKind::Dir(ref children) => children.get(parts_iter.next()
                                                                        .expect("peek2 is Some, next is None")
                                                                        .as_normal()
                                                                        .expect("parts_iter should be Normal after up_path"))
                                                         .cloned()
                                                         .ok_or_else(ENOENT)?,

                    // We are at a symlink! We have to traverse the symlink before we can continue
                    // with parts_iter.
                    DeKind::Symlink(ref sl) => {
                        let (fs, may_base) = (&FileSystem {
                            root: self.root.clone(),
                            pwd:  fs.clone(),
                        }).traverse(path_parts::normalize(sl), level)?;
                        match may_base {
                            Some(base) => {
                                let parts: path_parts::Parts = Part::Normal(base).into();
                                // The returned fs traversed the symlink up to the base directory.
                                // It may now be at a symlink, that is fine.
                                //
                                // The symlink had a base directory that we did not traverse. We
                                // need to push that to the front of our parts_iter.
                                //
                                // parts_iter is a Peek2able<path_parts::PartsIntoIter>. We can't
                                // just blindly chain our new iterator (of one) into the existing
                                // parts_iter because the types are different.
                                //
                                // Since we don't really care about inefficiencies too much (the
                                // only reasonable usage of a symlink in an in-memory filesystem
                                // would be for testing...), we'll just be inefficient.
                                parts_iter = parts.into_iter()
                                                  .chain(parts_iter)
                                                  .collect::<path_parts::Parts>()
                                                  .into_iter()
                                                  .peek2able();
                            },
                            None => {
                                if path_empty(sl) {
                                    panic!("empty path in a symlink (should not be possible)");
                                }
                                // The symlink was either the root directory or entirely parent
                                // directories. The returned fs is at the proper location. We do
                                // nothing!
                            }
                        };
                        // Now that we have traversed the symlink and potentially pushed its
                        // un-traversed base path to the front of parts_iter, return fs.
                        fs
                    }

                    // We are at a file, so we cannot traverse.
                    _ => return Err(ENOTDIR()),
                }
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

    // cd changes the filesystems current working directory (cwd). TODO: we need to remember if we
    // are in a symlink. This may be "easy" by simply keeping the normalized path that we are at
    // and always appending to that at all times, cleaning up every time.
    //
    // This function takes a recursion level as it may be recursive if the end of path is a symlink.
    fn cd<P: AsRef<Path>>(&mut self, path: P, level: &mut u8) -> Result<()> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path), level)?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Ok(());
                } else { // the path resulted in root or parent directories only
                    self.pwd = fs;
                    return Ok(());
                }
            }
        };
        let fs = fs.read();
        match fs.kind.dir_ref().get(&base) {
            Some(child) => {
                match child.read().kind {
                    DeKind::File(_) => return Err(ENOTDIR()),
                    DeKind::Symlink(ref sl) => {
                        let og_pwd = self.pwd.clone();
                        self.pwd = child.clone();
                        if {*level += 1; *level} == 40 {
                            return Err(ELOOP());
                        }
                        let res = self.cd(sl, level);
                        if res.is_err() {
                            self.pwd = og_pwd;
                            res?;
                        }
                        return Ok(())
                    },
                    _ => (),
                }
                self.pwd = child.clone();
                Ok(())
            }
            None => Err(ENOENT()),
        }
    }

    // create_dir creates directories, failing is the directory exists and can_exist is false.
    fn create_dir<P: AsRef<Path>>(&self, path: P, mode: u32, can_exist: bool) -> Result<()> {
        let mut level = 0;
        let (fs, may_base) = self.traverse(path_parts::normalize(&path), &mut level)?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else { // fs is at either root or a parent directory
                    if can_exist {
                        return Ok(());
                    }
                    return Err(EEXIST());
                }
            }
        };

        {
            let fs = fs.read();
            if !fs.executable() || !fs.writable() {
                return Err(EACCES());
            }
        }

        let mut borrow = fs.write();
        match borrow.kind.dir_mut().entry(base) {
            Entry::Occupied(o) => {
                if can_exist && o.get().read().is_dir() {
                    return Ok(());
                }
                Err(EEXIST())
            }
            Entry::Vacant(v) => {
                v.insert(Arc::new(RwLock::new(Dirent {
                    parent: Arc::downgrade(&fs),
                    kind:   DeKind::Dir(HashMap::new()),
                    mode:   mode,
                })));
                Ok(())
            }
        }
    }

    fn create_dir_all<P: AsRef<Path>>(&self, path: P, mode: u32) -> Result<()> {
        let (_, parts) = self.up_path(path_parts::normalize(&path))?;
        let mut path_buf = PathBuf::new();
        for part in parts {
            path_buf.push(part.into_normal().expect("parts_iter after up_path should only be Normal"));
            self.create_dir(&path_buf, mode, true)?;
        }
        Ok(())
    }

    // I would have thought this required read permissions, but...
    //
    // "No permissions are required on the file itself, but—in the case of stat() ... execute
    // (search) permission is required on all of the directories in pathname that lead to the file.
    //
    // (see http://man7.org/linux/man-pages/man2/stat.2.html)
    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Metadata> {
        let mut level = 0;
        let (fs, may_base) = self.traverse(path_parts::normalize(&path), &mut level)?;
        let fs = fs.read();
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(path) {
                    return Err(ENOENT());
                } else { // this is either the root dir or a parent dir
                    return Ok(Metadata {
                        filetype: FileType(Ftyp::Dir),
                        perms:    Permissions::from_mode(fs.mode),
                        length:   DIRLEN,
                    });
                }
            }
        };

        if !fs.executable() {
            return Err(EACCES());
        }

        match fs.kind.dir_ref().get(&base) {
            Some(child) => {
                let child = child.read();
                Ok(match child.kind {
                    DeKind::Dir(_) => Metadata {
                        filetype: FileType(Ftyp::Dir),
                        length:   DIRLEN,
                        perms:    Permissions::from_mode(child.mode),
                    },
                    DeKind::File(ref f) => Metadata {
                        filetype: FileType(Ftyp::File),
                        length:   f.read().data.len() as u64,
                        perms:    Permissions::from_mode(child.mode),
                    },
                    DeKind::Symlink(_) => Metadata {
                        filetype: FileType(Ftyp::Symlink),
                        length:   SYMLEN,
                        perms:    Permissions::from_mode(child.mode),
                    },
                })
            }
            None => Err(ENOENT()),
        }

    }

    // read_dir implements, essentially, `ls`, traversing symlinks as necessary.
    //
    // This function takes a recursion level as it may be recursive if the end of path is a symlink.
    fn read_dir<P: AsRef<Path>>(&self, path: P, level: &mut u8) -> Result<ReadDir> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path), level)?;
        let fs = fs.read();
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else { // path resolved to root or parent paths
                    return ReadDir::new(&path, &*fs);
                }
            }
        };

        match fs.kind.dir_ref().get(&base) {
            Some(child) => {
                let borrow = child.read();
                // If the base of the path is a symlink, we ReadDir that.
                if let DeKind::Symlink(ref sl) = borrow.kind {
                    if {*level += 1; *level} == 40 {
                        return Err(ELOOP());
                    }
                    return (&FileSystem {
                        root: self.root.clone(),
                        pwd:  child.clone(),
                    }).read_dir(sl, level);
                }
                // Otherwise, we ReadDir whatever this is. ReadDir::new bails with ENOTDIR if it is
                // given a file.
                ReadDir::new(&path, &borrow)
            },
            None => Err(ENOENT()),
        }
    }

    fn remove<P: AsRef<Path>>(&self, path: P, kind: FileType) -> Result<()> {
        let mut level = 0;
        let (fs, may_base) = self.traverse(path_parts::normalize(&path), &mut level)?;
        let base = may_base.ok_or_else(|| if path_empty(&path) {
                                              ENOENT()
                                          } else {
                                              ENOTEMPTY()
                                          })?;

        {
            let fs = fs.read();
            if !fs.executable() || !fs.writable() {
                return Err(EACCES());
            }
        }

        // We need to make sure that the FileType being requested for removal matches the FileType
        // of the directory. Scope this check so it drops before we mutate.
        {
            let fs = fs.read();
            let child = fs.kind
                          .dir_ref()
                          .get(&base)
                          .ok_or_else(ENOENT)?
                          .read();

            match kind.0 {
                // Symlinks and files are just simply removed, but directories must be empty.
                Ftyp::File | Ftyp::Symlink => if child.is_dir() { return Err(EISDIR()); },
                Ftyp::Dir => {
                    if !child.is_dir() {
                        return Err(ENOTDIR());
                    }
                    if !child.kind.dir_ref().is_empty() {
                        return Err(ENOTEMPTY());
                    }
                },
            }
        }

        fs.write().kind.dir_mut().remove(&base);
        Ok(())
    }
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.remove(path, FileType(Ftyp::File))
    }
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.remove(path, FileType(Ftyp::Dir))
    }

    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        // Rust's remove_dir_all is actually very weak (weaker than rm -r). Rust relies on read_dir
        // to recurse, which requires `ls`. Standard linux is able to remove empty directories with
        // only write and execute privileges. This code attempts to mimic what Rust will do.
        fn recursive_remove(fs: Arc<RwLock<Dirent>>) -> Result<()> {
            let mut fs = fs.write();
            let accessible = fs.readable() && fs.executable() && fs.writable();
            match fs.kind {
                DeKind::Dir(ref mut children) => {
                    if !accessible {
                        return Err(EACCES());
                    }

                    // We recursively remove until we encounter an error. Only after recursing do
                    // we remove everything from fs's HashMap that we successfully deleted.
                    let mut deleted = Vec::new();
                    let res: Result<()> = {
                        let mut child_names = Vec::new();
                        for child in children.iter() {
                            child_names.push(child);
                        }
                        // recursive removes work alphabetically
                        child_names.sort_by_key(|&(k, _)| k);

                        let mut err = None;
                        for &(child_name, child) in &child_names {
                            match recursive_remove(child.clone()) {
                                Ok(_) => deleted.push(child_name.clone()),
                                Err(e) => {
                                    err = Some(e);
                                    break;
                                },
                            }
                        }
                        match err {
                            Some(e) => Err(e),
                            None => Ok(()),
                        }
                    };
                    // We have to remove everything we successfully recursively deleted.
                    for child_name in deleted {
                        children.remove(&child_name);
                    }
                    res?
                }
                DeKind::File(ref mut f) => f.write().invalidate(),
                DeKind::Symlink(_) => (), // symlinks are never recursively traversed
            }
            Ok(())
        }

        let mut level = 0;
        let (fs, may_base) = self.traverse(path_parts::normalize(&path), &mut level)?;
        match may_base {
            Some(base) => { // removing a non-root path
                let mut fs = fs.write();
                if !fs.executable() || !fs.writable() {
                    return Err(EACCES());
                }
                let children = fs.kind.dir_mut();
                if let Entry::Occupied(child) = children.entry(base) {
                    recursive_remove(child.get().clone())?;
                    child.remove();
                }
            }
            None => { // removing either a direct parent directory or everything under root.
                if path_empty(&path) {
                    return Err(ENOENT());
                }
                // TODO we can remove the fs under us. This is valid, but future IO operations
                // should completely fail unless we are at root and root is what remains.
                recursive_remove(fs.clone())?;
            }
        }
        Ok(())
    }

    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        let mut level = 0;
        let (old_fs, old_may_base) = self.traverse(path_parts::normalize(&from), &mut level)?;
        let old_base = old_may_base.ok_or_else(|| if path_empty(&from) {
                                                      ENOENT()
                                                  } else {
                                                      if !Arc::ptr_eq(&old_fs, &self.root) {
                                                          // Renaming purely through parent
                                                          // directories returns EBUSY.
                                                          EBUSY()
                                                      } else {
                                                          // I really don't want to support this,
                                                          // nor manually test what can happen.
                                                          Error::new(ErrorKind::Other,
                                                                     "rename of root unimplemented")
                                                      }
                                                  })?;
        level = 0;
        let (new_fs, new_may_base) = self.traverse(path_parts::normalize(&to), &mut level)?;
        let new_base =
            new_may_base.ok_or_else(|| if path_empty(&to) { ENOENT() } else { EEXIST() })?;

        if Arc::ptr_eq(&old_fs, &new_fs) && old_base == new_base {
            return Ok(());
        }

        {
            let old_fs = old_fs.read();
            if !old_fs.executable() || !old_fs.writable() {
                return Err(EACCES());
            }
            let new_fs = new_fs.read();
            if !new_fs.executable() || !new_fs.writable() {
                return Err(EACCES());
            }
        }

        // Rust's rename is strong, but also annoying, in that it can rename a directory to a
        // directory if that directory is empty. We could make the code elegant, but this will do.
        let (old_exist, old_is_dir) =
            match old_fs.read().kind.dir_ref().get(&old_base) {
                Some(child) => (true, child.read().is_dir()),
                None => (false, false),
            };

        if !old_exist {
            return Err(ENOENT());
        }

        let (new_exist, new_is_dir, new_is_empty) =
            match new_fs.read().kind.dir_ref().get(&new_base) {
                Some(child) => {
                    match child.read().kind {
                        DeKind::Dir(ref children) => (true, true, children.is_empty()),
                        _ => (true, false, false),
                    }
                }
                None => (false, false, false),
            };

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

        let removed = old_fs.write().kind.dir_mut().remove(&old_base)
                                              .expect("logic verifying dirent existence is wrong");
        new_fs.write().kind.dir_mut().insert(new_base, removed);
        Ok(())
    }

    // set_permissions implements chmod, traversing symlinks as necessary.
    //
    // This function takes a recursion level as it may be recursive if the end of path is a symlink.
    fn set_permissions<P: AsRef<Path>>(&self, path: P, mode: u32, level: &mut u8) -> Result<()> {
        let (fs, may_base) = self.traverse(path_parts::normalize(&path), level)?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else {
                    // symlinks are always 0o777. If traverse returns no base, path resolved to
                    // (and fs is) either the root directory or a parent directory. This is
                    // concrete (not a symlink), so we can set its mode.
                    fs.write().mode = mode;
                    return Ok(());
                }
            }
        };
        let fs = fs.write();
        match fs.kind.dir_ref().get(&base) {
            Some(child) => {
                // as documented just above, we cannot change the permissions of symlinks.
                // set_permissions on symlinks actually changes what they link to, so, well, we
                // have to do that here.
                if let DeKind::Symlink(ref sl) = child.read().kind {
                    if {*level += 1; *level} == 40 {
                        return Err(ELOOP());
                    }
                    return (&FileSystem{
                        root: self.root.clone(),
                        pwd:  child.clone(),
                    }).set_permissions(sl, mode, level);
                }
                child.write().mode = mode;
                Ok(())
            }
            None => Err(ENOENT()),
        }
    }

    // open has to take the master filesystem (FS) because File itself can call set_permissions.
    // There is probably an avenue to clean this up.
    fn open<P: AsRef<Path>>(&self,
                            master_fs: FS,
                            path: P,
                            options: &OpenOptions,
                            level: &mut u8)
                            -> Result<File> {
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

        // Now, on with (potentially) opening.
        let (fs, may_base) = self.traverse(path_parts::normalize(&path), level)?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                } else { // root or parent directories only (both of which,
                         // being dirs, fail immediately in open_existing)
                    return Self::open_existing(master_fs, path, &fs, &options);
                }
            }
        };
        if !fs.read().executable() {
            return Err(EACCES());
        }

        // If the file exists, open it.
        if let Some(child) = fs.read().kind.dir_ref().get(&base) {
            if let DeKind::Symlink(ref sl) = child.read().kind {
                // Bummer, the base of our path is a symlink. Open that.
                if {*level += 1; *level} == 40 {
                    return Err(ELOOP());
                }
                return (&FileSystem {
                    root: self.root.clone(),
                    pwd:  fs.clone(),
                }).open(master_fs, sl, &options, level);
            }
            return Self::open_existing(master_fs, path, child, &options);
        }

        // From here down, we worry about creating a new file.
        if !fs.read().writable() {
            return Err(EACCES());
        }
        if !options.create {
            return Err(ENOENT());
        }
        let file = Arc::new(RwLock::new(RawFile { // backing "inode" file
            valid: true,
            data:  Vec::new(),
        }));
        let child = Arc::new(RwLock::new(Dirent { // hard link
            parent: Arc::downgrade(&fs),
            kind:   DeKind::File(file.clone()),
            mode:   options.mode,
        }));
        fs.write().kind.dir_mut().insert(base, child);
        Ok(File { // file view
            fs:   master_fs,
            path: path.as_ref().to_owned(),

            read:   options.read,
            write:  options.write,
            append: options.append,

            metadata: Metadata {
                filetype: FileType(Ftyp::File),
                length:   0,
                perms:    Permissions::from_mode(options.mode),
            },

            cursor: Arc::new(Mutex::new(FileCursor {
                file: file.clone(),
                at:   0,
            })),
        })
    }

    // `open_existing` opens known existing file with the given options, returning an error if the
    // file cannot be opened with those options. This takes the master filesystem (FS) for the same
    // reason open does: a File has set_permissions, which needs the FS...
    fn open_existing<P: AsRef<Path>>(master_fs: FS,
                                     path: P,
                                     fs: &Arc<RwLock<Dirent>>,
                                     options: &OpenOptions)
                                     -> Result<File> {
        if options.excl {
            return Err(EEXIST());
        }

        let fs = fs.read();
        // we panic below if fs is a symlink
        if fs.is_dir() {
            if options.write {
                return Err(EISDIR());
            }
            // TODO we could return Ok here so that users can stat the File, but that is more
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
            let arc_file = fs.kind.file_ref().clone();
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
            fs:   master_fs,
            path: path.as_ref().to_owned(),

            read:   read,
            write:  write,
            append: options.append,

            metadata: Metadata {
                filetype: FileType(Ftyp::File),
                length: len as u64,
                perms: Permissions::from_mode(options.mode),
            },

            cursor: Arc::new(Mutex::new(FileCursor {
                file: file,
                at:   0,
            })),
        })
    }
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
        // First, we prove our filesystem comparison operations work.
        // TODO add a symlink here
        let exp_pwd = Arc::new(RwLock::new(Dirent {
            parent: Weak::new(),
            kind:   DeKind::Dir(HashMap::new()),
            mode:   0,
        }));

        let exp = FS {
            inner: Arc::new(Mutex::new(FileSystem {
                root: exp_pwd.clone(),
                pwd:  exp_pwd,
            })),
        };
        {
            let ref mut root_rc = exp.inner.lock().pwd;
            let mut root = root_rc.write();
            let ref mut dir = root.kind.dir_mut();
            dir.insert(OsString::from("lolz"),
                        Arc::new(RwLock::new(Dirent {
                            parent: Arc::downgrade(&root_rc),
                            kind:   DeKind::Dir(HashMap::new()),
                            mode:   0o666,
                        })));
            dir.insert(OsString::from("f"),
                        Arc::new(RwLock::new(Dirent{
                            parent: Arc::downgrade(&root_rc),
                            kind:   DeKind::File(Arc::new(RwLock::new(RawFile{
                                valid: false,
                                data:  vec![1, 2, 3],
                            }))),
                            mode:   0o334,
                        })));
        }

        let fs = FS::with_mode(0o777);
        assert!(fs.new_dirbuilder().mode(0o666).create("lolz").is_ok());
        let mut f = fs.new_openopts().mode(0o334).write(true).create_new(true).open("f").unwrap();
        assert!(f.write(vec![1, 2, 3].as_slice()).is_ok());
        assert!(fs.set_permissions("/", Permissions::from_mode(0)).is_ok());
        assert!(fs == exp);
    }

    #[test]
    fn create_dir() {
        // We just proved that file system comparisons work. Let's build a slightly more
        // complicated filesystem and then prove create_dir works.
        let exp_pwd = Arc::new(RwLock::new(Dirent {
            parent: Weak::new(),
            kind:   DeKind::Dir(HashMap::new()),
            mode:   0o300,
        }));
        let exp = FS {
            inner: Arc::new(Mutex::new(FileSystem {
                root: exp_pwd.clone(),
                pwd:  exp_pwd,
            })),
        };

        {
            let ref mut root = exp.inner.lock().pwd;
            let mut borrow = root.write();
            let children = borrow.kind.dir_mut();
            children.insert(OsString::from("a"),
                            Arc::new(RwLock::new(Dirent {
                                parent: Arc::downgrade(&root),
                                kind:   DeKind::Dir(HashMap::new()),
                                mode:   0o500, // r-x: cannot create subfiles
                            })));
            children.insert(OsString::from("b"),
                            Arc::new(RwLock::new(Dirent {
                                parent: Arc::downgrade(&root),
                                kind:   DeKind::Dir(HashMap::new()),
                                mode:   0o600, // rw-: cannot exec (cd) into to create subfiles
                            })));
            let child = Arc::new(RwLock::new(Dirent {
                parent: Arc::downgrade(&root),
                kind:   DeKind::Dir(HashMap::new()),
                mode:   0o300, // _wx: all we need
            }));
            {
                let mut child_borrow = child.write();
                let child_children = child_borrow.kind.dir_mut();
                child_children.insert(OsString::from("d"),
                                      Arc::new(RwLock::new(Dirent {
                                          parent: Arc::downgrade(&child),
                                          kind:   DeKind::Dir(HashMap::new()),
                                          mode:   0o777,
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
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("a/z").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("b/z").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("").unwrap_err(),    ENOENT()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("/").unwrap_err(),   EEXIST()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("a").unwrap_err(),   EEXIST()));
        assert!(errs_eq(fs.new_dirbuilder().mode(0o777).create("z/z").unwrap_err(), ENOENT()));
    }

    #[test]
    fn create_dir_all() {
        // Now that we proved create_dir works, we can setup a more complicated testing system and
        // prove create_dir_all works.
        let fs = FS::with_mode(0o300);
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("////").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("a/b/c").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("/a/b/c/").is_ok());
        assert!(fs.new_dirbuilder().recursive(true).create("..").is_ok());
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
        // First, prove that open even works (even though we tested it in the first test).
        // Then, prove all combinations of OpenOptions work as expected.
        let fs = FS::with_mode(0o700);
        let exp = FS::with_mode(0o700);
        {
            let ref mut root = exp.inner.lock().pwd;
            root.write()
                .kind
                .dir_mut()
                .insert(OsString::from("a"),
                        Arc::new(RwLock::new(Dirent {
                            parent: Arc::downgrade(&root),
                            kind: DeKind::File(Arc::new(RwLock::new(RawFile {
                                valid: true,
                                data: vec![1, 2, 3, 4],
                            }))),
                            mode: 0o300,
                        })));
        }
        let mut file = fs.new_openopts().create(true).write(true).mode(0o300).open("a").unwrap();
        assert!(file.write(vec![1, 2, 3, 4].as_slice()).is_ok());

        assert!(fs.new_dirbuilder().mode(0o100).create("unwrite").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("unexec/subdir").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("okdir").is_ok());
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
        let mut on = || -> i32 { i += 1; i };
        // These next few blocks are a bit terse, but they test combinations of OpenOptions.
        // The format of the boolean parameters is (r)ead, (w)rite, (a)ppend, (t)runcate,
        // (e)xclusive [aka create_new], and (c)reate.
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
        test_open(on(), &fs, t, f, f, f, f, f, 0o700, "/", Some(Error::new(ErrorKind::Other, "")));
        assert!(fs.cd("okdir").is_ok());
        test_open(on(), &fs, t, f, f, f, f, f, 0o700, "..", Some(Error::new(ErrorKind::Other, "")));
        assert!(fs.cd("..").is_ok());

        // New files in unreachable directories...
        test_open(on(), &fs, f, t, f, f, t, f, 0o200, "unexec/a", Some(EACCES()));
        test_open(on(), &fs, f, t, f, f, t, f, 0o200, "unwrite/a", Some(EACCES()));

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
        test_open(on(), &fs, t, t, f, f, f, t, 0o300, "f_unread", Some(EACCES()));
        test_open(on(), &fs, f, t, f, f, f, t, 0o500, "f_unwrite", None); // w
        test_open(on(), &fs, f, t, f, f, f, t, 0o500, "f_unwrite", Some(EACCES()));
    }

    #[test]
    fn remove() {
        // Now we have proved creating things work. Let's prove destroying things works.
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

        // While we are here, quickly test that create_dir on an existing file fails - we did not
        // test above in create_dir as we were, at the time, proving create_dir worked exactly.
        assert!(errs_eq(fs.new_dirbuilder().mode(0o300).create("a/c").unwrap_err(),
                        EEXIST()));

        assert!(errs_eq(fs.remove_dir("").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.remove_dir("/").unwrap_err(), ENOTEMPTY()));
        assert!(errs_eq(fs.remove_dir("unexec/subdir").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.remove_dir("unexec/subdir/d").unwrap_err(), EACCES()));

        assert!(fs.cd("a").is_ok());
        assert!(errs_eq(fs.remove_dir("..").unwrap_err(), ENOTEMPTY()));
        assert!(fs.cd("..").is_ok());
        assert!(errs_eq(fs.remove_dir("a/c/z").unwrap_err(), ENOTDIR()));
        assert!(errs_eq(fs.remove_dir("a/z").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.remove_dir("a/d").unwrap_err(), ENOTEMPTY()));

        assert!(errs_eq(fs.cd("a/c").unwrap_err(), ENOTDIR()));
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
        // And now we ensure batch removes work as expected - specifically, an alphabetical remove
        // that fails when a subdirectory is not readable.
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
        assert!(errs_eq(fs.remove_dir_all("..").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.remove_dir_all("x").unwrap_err(), EACCES()));

        let exp = FS::with_mode(0o700);
        assert!(exp.new_dirbuilder().mode(0o500).create("x").is_ok());
        assert!(fs == exp);
    }

    #[test]
    fn rename() {
        // Rename can fail _a lot_.
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
        // Rote test to ensure ReadDir iteration works and is alphabetical.
        let fs = FS::with_mode(0o700);
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).create("a/b/d").is_ok());
        assert!(fs.new_dirbuilder().mode(0o100).create("a/b/z").is_ok());
        assert!(fs.new_openopts().mode(0o000).write(true).create(true).open("a/b/f").is_ok());

        let mut reader = fs.read_dir("a/b").unwrap();
        assert_eq!(reader.next().unwrap().unwrap(),
                   DirEntry {
                       dir:  PathBuf::from("a/b"),
                       base: OsString::from("c"),
                       meta: Metadata {
                           filetype: FileType(Ftyp::Dir),
                           length:   DIRLEN,
                           perms:    Permissions::from_mode(0o700),
                       },
                   });
        assert_eq!(reader.next().unwrap().unwrap(),
                   DirEntry {
                       dir:  PathBuf::from("a/b"),
                       base: OsString::from("d"),
                       meta: Metadata {
                           filetype: FileType(Ftyp::Dir),
                           length:   DIRLEN,
                           perms:    Permissions::from_mode(0o300),
                       },
                   });
        let next = reader.next().unwrap().unwrap();
        assert_eq!(next.path(), PathBuf::from("a/b/f"));
        assert_eq!(next.file_name(), OsString::from("f"));
        assert_eq!(next.metadata().unwrap(),
                   Metadata {
                       filetype: FileType(Ftyp::File),
                       length:   0,
                       perms:    Permissions::from_mode(0),
                   });
        let next = reader.next().unwrap().unwrap();
        assert_eq!(next.path(), PathBuf::from("a/b/z"));
        assert_eq!(next.file_name(), OsString::from("z"));
        assert_eq!(next.metadata().unwrap(),
                   Metadata {
                       filetype: FileType(Ftyp::Dir),
                       length:   DIRLEN,
                       perms:    Permissions::from_mode(0o100),
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

    #[test]
    fn test_usage() {
        // This test tests quite a few edge conditions.
        let fs = FS::with_mode(0o300);
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());

        let mut wf =
            fs.new_openopts().mode(0o600).write(true).create_new(true).open("a/f").unwrap();
        assert_eq!(wf.write(vec![0, 1, 2, 3, 4, 5].as_slice()).unwrap(), 6);
        assert_eq!(wf.seek(SeekFrom::Start(1)).unwrap(), 1);
        assert_eq!(wf.write(vec![1, 2, 3].as_slice()).unwrap(), 3);

        let mut rf = fs.new_openopts().read(true).open("a/f").unwrap();
        assert_eq!(rf.seek(SeekFrom::Current(1)).unwrap(), 1);

        let mut output = [0u8; 4];
        assert_eq!(rf.read(&mut output).unwrap(), 4);
        assert_eq!(&output, &[1, 2, 3, 4]);
        assert_eq!(rf.seek(SeekFrom::End(-4)).unwrap(), 2);
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
