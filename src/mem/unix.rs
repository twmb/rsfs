//! This module provides an in-memory filesystem that follows Unix semantics.
//!
//! This module, when used directly, is cross-platform. This module imitates a Unix filesystem as
//! closely as possible, meaning if you create a directory without executable permissions, you
//! cannot do anything inside of it.
//!
//! # Example
//!
//! ```
//! use std::io::{Read, Seek, SeekFrom, Write};
//! use std::path::PathBuf;
//!
//! use rsfs::*;
//! use rsfs::unix_ext::*;
//! use rsfs::mem::unix::FS;
//!
//! let fs = FS::new();
//! assert!(fs.create_dir_all("a/b/c").is_ok());
//!
//! // writing past the end of a file zero-extends to the write position
//! let mut wf = fs.create_file("a/f").unwrap();
//! assert_eq!(wf.write_at(b"hello", 100).unwrap(), 5);
//!
//! let mut rf = fs.open_file("a/f").unwrap();
//! let mut output = [1u8; 5];
//! assert_eq!(rf.read(&mut output).unwrap(), 5);
//! assert_eq!(&output, &[0, 0, 0, 0, 0]);
//!
//! assert_eq!(rf.seek(SeekFrom::Start(100)).unwrap(), 100);
//! assert_eq!(rf.read(&mut output).unwrap(), 5);
//! assert_eq!(&output, b"hello");
//! ```

extern crate parking_lot;

use self::parking_lot::{Mutex, RwLock};

use std::cmp::{self, Ordering};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ffi::OsString;
use std::fmt;
use std::io::{self, Error, ErrorKind, Read, Result, Seek, SeekFrom, Write};
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::SystemTime;
use std::vec::IntoIter;

use fs::{self, DirBuilder as _DirBuilder, FileType as _FileType, Metadata as _Metadata};
use unix_ext;

use errors::*;
use path_parts::{normalize, IteratorExt, Part, Parts};
use ptr::Raw;

/// `DIRLEN` is the length returned from `Metadata`s len() call for a directory. This is pulled
/// from the initial file size that Unix uses for a directory sector. This module does not attempt
/// to return a larger number if the directory contains many children with long names.
const DIRLEN: usize = 4096;

/// A builder used to create directories in various manners.
///
/// This builder implements [`rsfs::DirBuilder`] and supports [unix extensions].
///
/// [`rsfs::DirBuilder`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.DirBuilder.html
/// [unix extensions]: https://docs.rs/rsfs/0.2.0/rsfs/unix_ext/trait.DirBuilderExt.html
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # use rsfs::mem::FS;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
/// let db = fs.new_dirbuilder();
/// db.create("dir")?;
/// # Ok(())
/// # }
/// ```
#[derive(Clone, Debug)]
pub struct DirBuilder {
    /// fs is what we reach inside to create our directory.
    fs: FS,
    /// recursive indicates that nested directories will be created recursively.
    recursive: bool,
    /// mode is the unix mode to set on directories when creating them.
    mode:      u32,
}

impl fs::DirBuilder for DirBuilder {
    fn recursive(&mut self, recursive: bool) -> &mut Self {
        self.recursive = recursive; self
    }
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        if self.recursive {
            self.fs.0.lock().create_dir_all(path, self.mode)
        } else {
            self.fs.0.lock().create_dir(path, self.mode, false)
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
/// An instance of `DirEntry` implements [`rsfs::DirEntry`] and represents an entry inside a
/// directory on the in-memory filesystem.
///
/// [`rsfs::DirEntry`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.DirEntry.html
/// [`ReadDir`]: struct.ReadDir.html
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # use rsfs::mem::FS;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
/// for entry in fs.read_dir(".")? {
///     let entry = entry?;
///     println!("{:?}: {:?}", entry.path(), entry.metadata()?.permissions());
/// }
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct DirEntry {
    /// dir is the original path requested for ReadDir. We make no attempt to clean it.
    dir: PathBuf,
    /// base is the name of the file/dir/symlink at this dirent. This is created when making a
    /// DirEntry, meaning we do not track if the dirent was renamed immediately after creation.
    base: OsString,
    /// inode is the backing "inode" for this DirEntry. The metadata() and file_type() functions in
    /// std::fs actually do OS calls, meaning they work on the most up to date actual entry.
    inode: Inode,
}

impl fs::DirEntry for DirEntry {
    type Metadata = Metadata;
    type FileType = FileType;

    fn path(&self) -> PathBuf {
        self.dir.join(self.base.clone())
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        Ok(Metadata(*self.inode.read()))
    }
    fn file_type(&self) -> Result<Self::FileType> {
        Ok(self.inode.read().ftyp)
    }
    fn file_name(&self) -> OsString {
        self.base.clone()
    }
}

/// `RawFile` is the underlying contents of a file in our filesystem. `OpenOption`s .open() call
/// returns a view of a file. If a file is removed from the filesystem, currently open files can
/// still be read from or written to, but the file will not be openable anymore.
#[derive(Debug)]
struct RawFile {
    /// data is the backing file data.
    data: Vec<u8>,
    /// inode allows us to read and write the most up to date metadata.
    inode: Inode,
}

impl RawFile {
    /// read_at reads contents of the file into dst from a given index in the file.
    fn read_at(&self, at: usize, dst: &mut [u8]) -> Result<usize> {
        self.inode.write().times.update(ACCESSED);

        let data = &self.data;
        if at > data.len() {
            return Ok(0);
        }

        let unread = &data[at..];
        let copy_size = cmp::min(dst.len(), unread.len());

        dst[..copy_size].copy_from_slice(&unread[..copy_size]);
        Ok(copy_size)
    }

    /// write_at writes to the RawFile at a given index, zero extending the existing data if
    /// necessary.
    fn write_at(&mut self, at: usize, src: &[u8]) -> Result<usize> {
        if src.is_empty() {
            return Ok(0)
        }

        let mut dst = &mut self.data;
        if at > dst.len() {
            let mut new = vec![0; at + src.len()];
            new[..dst.len()].copy_from_slice(dst);
            *dst = new;
        }

        let new_end = src.len() + at;
        if dst.len() >= new_end {
            dst[at..new_end].copy_from_slice(src);
        } else {
            dst.truncate(at);
            dst.extend_from_slice(src);
        }
        let mut inode = self.inode.write();
        inode.times.update(MODIFIED);
        inode.length = dst.len();
        Ok(src.len())
    }
}

/// A view into a file on the filesystem.
///
/// An instance of `File` can be read or written to depending on the options it was opened with.
/// Files also implement `Seek` to alter the logical cursor position of the internal file.
///
/// This struct implements [`rsfs::File`] and has [unix extensions].
///
/// [`rsfs::File`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.File.html
/// [unix extensions]: https://docs.rs/rsfs/0.2.0/rsfs/unix_ext/trait.FileExt.html
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # use rsfs::mem::FS;
/// # use std::io::Write;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
/// let mut f = fs.create_file("f")?;
/// assert_eq!(f.write(&[1, 2, 3])?, 3);
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct File {
    /// read indicates this file view can read the underlying file.
    read:   bool,
    /// read indicates this file view can write to the underlying file.
    write:  bool,
    /// read indicates this file view will append to the current end of the underlying file on
    /// every write.
    append: bool,

    /// cursor is wrapped in an `Arc<Mutex<_>>` solely to support `File`s probably-never-used
    /// `try_clone` function.
    cursor: Arc<Mutex<FileCursor>>,
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
        let cursor = self.cursor.lock();
        let file = cursor.file.read();
        let meta = Metadata(*file.inode.read());
		Ok(meta)
    }

    fn try_clone(&self) -> Result<Self> {
        Ok(File {
            read:   self.read,
            write:  self.write,
            append: self.append,
            cursor: self.cursor.clone(),
        })
    }

    fn set_permissions(&self, perms: Self::Permissions) -> Result<()> {
        let cursor = self.cursor.lock();
        let file = cursor.file.write();
        let mut inode = file.inode.write();
        inode.perms = perms;
        Ok(())
    }
}

/// `FileCursor` corresponds to an actual file descriptor, which, "behind the scenes", keeps track
/// of where we are in a file. We use a `FileCursor` to support File's cloning and to support
/// implementing read/write/seek on a &'a File.
#[derive(Debug)]
struct FileCursor {
    /// file is the actual underlying file. It is wrapped in an `Arc<RwLock<>>` because other file
    /// handles can also be reading to or writing to this file.
    file: Arc<RwLock<RawFile>>,
    /// at tracks this cursor's position in the underlying file.
    at:   usize,
}

impl FileCursor {
    /// The backing function for `File`s `set_len`, this can function runcate or zero extend the
    /// underlying file.
    fn set_len(&mut self, size: u64) -> Result<()> {
        let mut file = self.file.write();
        file.inode.write().times.update(MODIFIED);

        let size = size as usize;
        match file.data.len().cmp(&size) {
            Ordering::Less => {
                // If data is smaller, create a longer Vec and copy the original contents over.
                // This borrows from RawFile's write_at.
                let mut new = vec![0; size];
                new[..file.data.len()].copy_from_slice(&file.data);
                file.data = new;
            }
            // If data is longer, simply truncate it.
            Ordering::Greater => file.data.truncate(size),
            // If equal, we get to do nothing.
            _ => (),
        }
        Ok(())
    }

    /// The backing function for `File`s `read`.
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let n = self.file.read().read_at(self.at, buf)?;
        self.at += n;
        Ok(n)
    }

    /// The backing function for `File`s `write`.
    fn write(&mut self, buf: &[u8], append: bool) -> Result<usize> {
        let mut file = self.file.write();
        if append {
            self.at = file.data.len();
        }
        let n = file.write_at(self.at, buf)?;
        self.at += n;
        Ok(n)
    }

    /// The backing function for `File`s `seek`. While it is undefined to seek past the end of the
    /// file, we attempt to emulate what appears to be Rust's/Unix's behavior.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        let file = self.file.write();
        file.inode.write().times.update(ACCESSED);

        let len = file.data.len();
        // seek seemingly returns (if successful) the sum of the position we are seeking from and
        // the offset even if we seek past the end of the file.
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
        (&mut &*self).read(buf)
    }
}
impl Write for File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        (&mut &*self).write(buf)
    }
    fn flush(&mut self) -> Result<()> {
        (&mut &*self).flush()
    }
}
impl Seek for File {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        Ok(self.cursor.lock().seek(pos)?)
    }
}

// Now we actually do the impls for &'a File.

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

/// `Ftyp` is the actual underlying enum for a `FileType`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Ftyp {
    File,
    Dir,
    Symlink,
}

/// Returned from [`Metadata::file_type`], this structure represents the type of a file.
///
/// This structure implements [`rsfs::FileType`]
///
/// [`Metadata::file_type`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.Metadata.html#tymethod.file_type
/// [`rsfs::FileType`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.FileType.html
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # use rsfs::mem::FS;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
/// let f = fs.create_file("f")?;
/// assert!(fs.metadata("f")?.file_type().is_file());
/// # Ok(())
/// # }
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FileType(Ftyp);

impl fs::FileType for FileType {
    fn is_dir(&self) -> bool {
        self.0 == Ftyp::Dir
    }
    fn is_file(&self) -> bool {
        self.0 == Ftyp::File
    }
    fn is_symlink(&self) -> bool {
        self.0 == Ftyp::Symlink
    }
}

/// Metadata information about a file.
///
/// This structure, which implements [`rsfs::Metadata`], is returned from the [`metadata`] or
/// [`symlink_metadata`] methods and represents known metadata information about a file at the
/// instant in time this structure is instantiated.
///
/// [`rsfs::Metadata`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.Metadata.html
/// [`metadata`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.GenFS.html#tymethod.metadata
/// [`symlink_metadata`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.GenFS.html#tymethod.symlink_metadata
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # use rsfs::mem::FS;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
/// fs.create_file("f")?;
/// println!("{:?}", fs.metadata("f")?);
/// # Ok(())
/// # }
#[derive(Clone, Debug)]
pub struct Metadata(InodeData); // Metadata is a copy of InodeData at a point in time.

impl fs::Metadata for Metadata {
    type Permissions = Permissions;
    type FileType    = FileType;

    fn file_type(&self) -> Self::FileType {
        self.0.ftyp
    }
    fn is_dir(&self) -> bool {
        self.0.ftyp.is_dir()
    }
    fn is_file(&self) -> bool {
        self.0.ftyp.is_file()
    }
    fn len(&self) -> u64 {
        self.0.length as u64
    }
    fn permissions(&self) -> Self::Permissions {
        self.0.perms
    }
    fn modified(&self) -> Result<SystemTime> {
        Ok(self.0.times.modified)
    }
    fn accessed(&self) -> Result<SystemTime> {
        Ok(self.0.times.accessed)
    }
    fn created(&self) -> Result<SystemTime> {
        Ok(self.0.times.created)
    }
}

/// Options and flags which can be used to configure how a file is opened.
///
/// This builder, created from `GenFS`s [`new_openopts`], exposes the ability to configure how a
/// [`File`] is opened and what operations are permitted on the open file. `GenFS`s [`open_file`]
/// and [`create_file`] methods are aliases for commonly used options with this builder.
///
/// This builder implements [`rsfs::OpenOptions`] and supports [unix extensions].
///
/// [`new_openopts`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.GenFS.html#tymethod.new_openopts
/// [`open_file`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.GenFS.html#tymethod.open_file
/// [`create_file`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.GenFS.html#tymethod.create_file
/// [`rsfs::OpenOptions`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.OpenOptions.html
/// [unix extensions]: https://docs.rs/rsfs/0.2.0/rsfs/unix_ext/trait.OpenOptionsExt.html
///
/// # Examples
///
/// Opening a file to read:
///
/// ```
/// # use rsfs::*;
/// # use rsfs::mem::FS;
/// # fn foo() -> std::io::Result<()> {
/// # let fs = FS::new();
/// let f = fs.new_openopts()
///           .read(true)
///           .open("f")?;
/// # Ok(())
/// # }
/// ```
///
/// Opening a file for both reading and writing, as well as creating it if it doesn't exist:
///
/// ```
/// # use rsfs::*;
/// # use rsfs::mem::FS;
/// # fn foo() -> std::io::Result<()> {
/// # let fs = FS::new();
/// let mut f = fs.new_openopts()
///               .read(true)
///               .write(true)
///               .create(true)
///               .open("f")?;
/// # Ok(())
/// # }
/// ```
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
        self.fs.0.lock().open(path, self, &mut 0)
    }
}

impl unix_ext::OpenOptionsExt for OpenOptions {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.mode = mode; self
    }
    fn custom_flags(&mut self, _: i32) -> &mut Self {
        self // we do nothing with these flags yet.
    }
}

/// Representation of the various permissions on a file.
///
/// This struct implements [`rsfs::Permissions`] and has [unix extensions].
///
/// [`rsfs::Permissions`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.Permissions.html
/// [unix extensions]: https://docs.rs/rsfs/0.2.0/rsfs/unix_ext/trait.PermissionsExt.html
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # use rsfs::mem::FS;
/// use rsfs::unix_ext::*;
/// use rsfs::mem::Permissions;
/// # fn foo() -> std::io::Result<()> {
/// # let fs = FS::new();
/// # fs.create_file("foo.txt")?;
///
/// fs.set_permissions("foo.txt", Permissions::from_mode(0o400))?;
/// # Ok(())
/// # }
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Permissions(u32);

impl fs::Permissions for Permissions {
	// readonly and set_readonly are odd: https://github.com/rust-lang/rust/issues/41984
    fn readonly(&self) -> bool {
        self.0 & 0o222 == 0
    }
    fn set_readonly(&mut self, readonly: bool) {
        if readonly {
            self.0 &= !0o222
        } else {
            self.0 |= 0o222
        }
    }
}

impl unix_ext::PermissionsExt for Permissions {
    fn mode(&self) -> u32 {
        self.0
    }
    fn set_mode(&mut self, mode: u32) {
        self.0 = mode
    }
    fn from_mode(mode: u32) -> Self {
        Permissions(mode)
    }
}

/// Iterator over entries in a directory.
///
/// This is returned from the [`read_dir`] method of `GenFS` and yields instances of
/// `io::Result<DirEntry>`. Through a [`DirEntry`], information about contents of a directory can
/// be learned.
///
/// [`read_dir`]: struct.FS.html#method.read_dir
/// [`DirEntry`]: struct.DirEntry.html
#[derive(Debug)]
pub struct ReadDir {
    ents: IntoIter<DirEntry>,
}

impl ReadDir {
    fn new<P: AsRef<Path>>(path: P, dir: &Dirent) -> Result<ReadDir> {
        if !dir.readable() {
            return Err(EACCES());
        }
        let children = match dir.kind {
            DeKind::Dir(ref children) => children,
            _ => return Err(ENOTDIR()),
        };

        // Most linux systems actually dont update atime on every read because that'd be pretty
        // expensive (note "relatime" when checking the output of `mount`). We do because it is
        // cheap to update an in-memory timestamp.
        dir.inode.write().times.update(ACCESSED);

        // Iterate over the children and create a bunch of DirEntrys as appropriate.
        let mut dirents = Vec::new();
        for (base, dirent) in children.iter() {
            dirents.push(DirEntry {
                dir:   PathBuf::from(path.as_ref()),
                base:  base.clone(),
                inode: dirent.inode.clone(),
            });
        }
        // read_dir usually returns dirents in alphabetical order, so we do too.
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

/// An in-memory struct that satisfies [`rsfs::GenFS`].
///
/// `FS` is thread safe and copyable. It operates internally with an `Arc<Mutex<FileSystem>>`
/// (`FileSystem` not being exported) and forces all filesystem calls to go through the mutex. `FS`
/// attempts to mimic all real errors that could occur on a filesystem. Generally, unless a `FS` is
/// setup with restrictive permissions, errors will only be encountered when operating on
/// non-existent filesystem entries or performing invalid oprations.
///
/// See the module [documentation] or every struct's documentation for more examples of using an
/// `FS`.
///
/// [`rsfs::GenFS`]: https://docs.rs/rsfs/0.2.0/rsfs/trait.GenFS.html
/// [documentation]: index.html
///
/// # Examples
///
/// ```
/// use rsfs::*;
/// use rsfs::mem::FS;
///
/// let fs = FS::new();
/// ```
#[derive(Clone, Debug)]
pub struct FS(Arc<Mutex<FileSystem>>);

/* The following is meant for debugging purposes when developing this library only
impl fmt::Display for FS {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let fs = self.0.lock();

        write!(f, "\nfilesystem\n----------\n")?;
        if !fs.pwd.alive {
            if Raw::ptr_eq(&fs.pwd.inner, &fs.root) {
                return write!(f, "deleted");
            }
        }

        let root = fs.root;

        fn wr(f: &mut fmt::Formatter, d: Raw<Dirent>, level: u32) -> fmt::Result {
            for _ in 0..level {
                write!(f, "    ")?;
            }
            let name = d.name.as_os_str().to_str().expect("expected utf8 dirent name");
            let inode = d.inode.view();
            match d.kind {
                DeKind::Dir(ref children) => {
                    write!(f, "{}/ -- {:o} (len: {})\n",
                        name, inode.perms.0, inode.length)?;
                    for child in children.values() {
                        wr(f, *child, level+1)?;
                    }
                    write!(f, "")
                }
                DeKind::File(_) => write!(f, "{} -- {:o} (len: {})\n",
                        name, inode.perms.0, inode.length),
                DeKind::Symlink(ref sl) => write!(f, "{}@->[{}] -- {:o} (len:{})\n",
                        name, sl.clone().to_str().expect("expected utf8 symlink name"),
                        inode.perms.0, inode.length),
            }
        }
        wr(f, root, 0)
    }
}
*/

impl FS {
    /// Creates an empty `FS` with mode `0o777`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rsfs::*;
    /// # use rsfs::mem::FS;
    /// let fs = FS::new();
    /// ```
    pub fn new() -> FS {
        Self::with_mode(0o777)
    }

    /// Creates an empty `FS` with the given mode.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rsfs::*;
    /// # use rsfs::mem::FS;
    /// let fs = FS::with_mode(0o300);
    /// ```
    pub fn with_mode(mode: u32) -> FS {
        let pwd = Raw::from(Dirent {
            parent: None,
            kind:   DeKind::Dir(HashMap::new()),
            name:   OsString::from(""),
            inode:  Inode::new(mode, Ftyp::Dir, DIRLEN),
        });
        FS(Arc::new(Mutex::new(FileSystem {
            root: pwd,
            pwd:  Pwd::from(pwd),
        })))
    }
}

impl Default for FS {
    fn default() -> Self {
        FS::new()
    }
}

impl fs::GenFS for FS {
    type DirBuilder  = DirBuilder;
    type DirEntry    = DirEntry;
    type File        = File;
    type Metadata    = Metadata;
    type OpenOptions = OpenOptions;
    type Permissions = Permissions;
    type ReadDir     = ReadDir;

    fn canonicalize<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        self.0.lock().canonicalize(path, &mut 0)
    }
    fn copy<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<u64> {
        // std::fs's copy actually uses std::fs functions to implement copy, which is nice. We will
        // repeat that pattern here, which requires us to use rsfs traits
        use fs::OpenOptions;
        use fs::File;
        // First, though, we have to validate that `from` is actually a file.
        fn not_file() -> Error {
            Error::new(ErrorKind::InvalidInput, "the source path is not an existing regular file")
        }

        let (from, to) = (from.as_ref(), to.as_ref());

        // Now we do our "is file" checking, scoping the lock, because most other functions below
        // this scope each use a lock.
        {
            let fs = &*self.0.lock();
            let (fs, may_base) = fs.traverse(normalize(&from), &mut 0)?;
            let base = may_base.ok_or_else(not_file)?;

            if !fs.executable() {
                return Err(EACCES());
            }
            match fs.kind.dir_ref().get(&base) {
                Some(child) => match child.kind {
                    DeKind::File(_) => (),
                    _ => return Err(not_file()),
                },
                None => return Err(not_file()),
            }
        }

        // Now we do what std::fs does. Note that the open on from is technically a race: a second
        // process could come in, remove from, and create a symlink with the same name. That would
        // be the only potential problem. The end result would be that the symlink's target is
        // copied, which really isn't a huge deal. If the race changed from to a directory, the
        // io::copy would fail, as reads on directories fail immediately.
        // (also see https://github.com/rust-lang/rust/issues/37885)
        let mut reader = self.new_openopts().read(true).open(from)?;
        let mut writer = self.new_openopts().write(true).truncate(true).create(true).open(to)?;
        let perm = reader.metadata()?.permissions();
        let ret = io::copy(&mut reader, &mut writer)?;
        self.set_permissions(to, perm)?;
        Ok(ret)
    }
    fn create_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.new_dirbuilder().create(path)
    }
    fn create_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.new_dirbuilder().recursive(true).create(path)
    }
    fn hard_link<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()> {
        self.0.lock().hard_link(src, dst)
    }
    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata> {
        self.0.lock().metadata(path, &mut 0)
    }
    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<Self::ReadDir> {
        self.0.lock().read_dir(&path, &path, &mut 0)
    }
    fn read_link<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        self.0.lock().read_link(path)
    }
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.0.lock().remove_dir(path)
    }
    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.0.lock().remove_dir_all(path)
    }
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.0.lock().remove_file(path)
    }
    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        self.0.lock().rename(from, to)
    }
    fn set_permissions<P: AsRef<Path>>(&self, path: P, perms: Self::Permissions) -> Result<()> {
        self.0.lock().set_permissions(path, perms, &mut 0)
    }
    fn symlink_metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata> {
        self.0.lock().symlink_metadata(path)
    }

    fn new_openopts(&self) -> Self::OpenOptions {
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
    fn new_dirbuilder(&self) -> Self::DirBuilder {
        DirBuilder {
            fs: self.clone(),

            recursive: false,
            mode:      0o777, // default per unix_ext
        }
    }

    fn open_file<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        use fs::OpenOptions;
        self.new_openopts().read(true).open(path.as_ref())
    }
    fn create_file<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        use fs::OpenOptions;
        self.new_openopts().write(true).create(true).truncate(true).open(path.as_ref())
    }
}

impl unix_ext::GenFSExt for FS {
    fn symlink<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()> {
        self.0.lock().symlink(src, dst)
    }
}

/// Times tracks the modified, accessed, and created time for a Dirent.
#[derive(Copy, Clone, Debug)]
struct Times {
    modified: SystemTime,
    accessed: SystemTime,
    created:  SystemTime,
}

/// Bitflag indicating a Dirent was modified.
const MODIFIED: u8 = 1; // modified time
/// Bitflag indicating a Dirent was accessed.
const ACCESSED: u8 = 2; // accessed time
/// Bitflag indicating a Dirent was created.
const CREATED:  u8 = 4; // created time

impl Times {
    fn new() -> Times {
        let now = SystemTime::now();
        Times {
            modified: now,
            accessed: now,
            created:  now,
        }
    }

    fn update(&mut self, fields: u8) {
        const MASK: u8 = !(MODIFIED | ACCESSED | CREATED);
        if fields & MASK != 0 {
            panic!("incorrect times update usage!")
        }
        let now = SystemTime::now();
        if fields & MODIFIED != 0 {
            self.modified = now;
        }
        if fields & ACCESSED != 0 {
            self.accessed = now;
        }
        if fields & CREATED != 0 {
            self.created = now;
        }
    }
}

/// `InodeData` is the backing shared data of an "inode". Unix systems can have multiple files
/// pointing to the same inode. We minimally mimic that in this code. We don't recreate a full unix
/// filesystem, but the following data is shared behind a mutex when creating hard links or raw
/// files.
#[derive(Copy, Clone, Debug)]
struct InodeData {
    times:  Times,
    perms:  Permissions,
    ftyp:   FileType,
    length: usize,
}

impl PartialEq for InodeData {
    fn eq(&self, other: &Self) -> bool {
        self.perms == other.perms &&
            self.ftyp == other.ftyp &&
            self.length == other.length
    }
}

/// `Inode` is what makes sharing `InodeData` between hard links / dirents / raw files possible.
#[derive(Clone, Debug)]
struct Inode(Arc<RwLock<InodeData>>);

impl PartialEq for Inode {
    fn eq(&self, other: &Self) -> bool {
        *self.read() == *other.read()
    }
}

impl Inode {
    fn new(mode: u32, ftyp: Ftyp, len: usize) -> Inode {
        Inode(Arc::new(RwLock::new(InodeData {
            times:  Times::new(),
            perms:  Permissions(mode),
            ftyp:   FileType(ftyp),
            length: len,
        })))
    }

    fn view(&self) -> InodeData {
        *self.read()
    }
    fn perms(&self) -> Permissions {
        self.read().perms
    }
}

impl Deref for Inode {
    type Target = Arc<RwLock<InodeData>>;

    #[inline]
    fn deref(&self) -> &Arc<RwLock<InodeData>> {
        &self.0
    }
}

/// `DeKind` differentiates between files, directories, and symlinks. It mildly duplicates
/// information that is available in `InodeData`s ftyp.
#[derive(Debug)]
enum DeKind {
    File(Arc<RwLock<RawFile>>),
    Dir(HashMap<OsString, Raw<Dirent>>),
    Symlink(PathBuf),
}

impl DeKind {
    fn file_ref(&self) -> &Arc<RwLock<RawFile>> {
        match *self {
            DeKind::File(ref f) => f,
            _ => panic!("file_ref used on DeKind when not a file"),
        }
    }
    fn dir_ref(&self) -> &HashMap<OsString, Raw<Dirent>> {
        match *self {
            DeKind::Dir(ref d) => d,
            _ => panic!("dir_ref used on DeKind when not a dir"),
        }
    }
    fn dir_mut(&mut self) -> &mut HashMap<OsString, Raw<Dirent>> {
        match *self {
            DeKind::Dir(ref mut d) => d,
            _ => panic!("dir_mut used on DeKind when not a dir"),
        }
    }
    fn symlink_ref(&self) -> &PathBuf {
        match *self {
            DeKind::Symlink(ref sl) => sl,
            _ => panic!("symlink_ref used on DeKind when not a symlink"),
        }
    }
}

/// Dirent represents all information needed at a node in our filesystem tree. We use raw pointers
/// to traverse dirents. It's "unsafe", so we have a myriad of tests ensuring it isn't.
///
/// We use `Raw` because the real alternative is `Arc<RwLock<_>>` around every Dirent (inside the
/// `HashMap` and inside the parent). Doing this would force a clone and a read lock on every
/// directory traversal. After writing all FS operations using `Arc`/`RwLock`, I am not so sure
/// that this is even safe - it's possible (and hard to reason about) that some combination of
/// directory traversals could hold a read lock blocking a write lock.
///
/// More importantly, having two filesystem operations occuring simultaneously is completely
/// unsafe. Think about what would happen if we need to rename something from /a/b/c to /d/e/f at
/// the same time that we are recursively removing /d. We would deadlock.
struct Dirent {
    parent: Option<Raw<Dirent>>,
    kind:   DeKind,
    name:   OsString,
    inode:  Inode,
}

// Functions implemented for Dirent basically all are helpers on reading the underlying inode data.
impl Dirent {
    fn is_dir(&self) -> bool {
        match self.kind {
            DeKind::Dir(_) => true,
            _ => false,
        }
    }
    fn readable(&self) -> bool {
        self.inode.perms().0 & 0o400 == 0o400
    }
    fn writable(&self) -> bool {
        self.inode.perms().0 & 0o200 == 0o200
    }
    fn executable(&self) -> bool {
        self.inode.perms().0 & 0o100 == 0o100
    }
    /// changeable implies executable and writable. Executable is always needed when attempting to
    /// write to a directory.
    fn changeable(&self) -> bool {
        self.inode.perms().0 & 0o300 == 0o300
    }
    /// Only recursive removes need completely open permissions.
    fn rremovable(&self) -> bool {
        self.inode.perms().0 & 0o700 == 0o700
    }
}

// Because of our tomfoolery with Raw pointers, we have to implement Debug manually to not have
// cycles through a Dirent's parent.
impl fmt::Debug for Dirent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Dirent {{ parent: ")?;
        match self.parent {
            Some(_) => write!(f, "Some(parent)")?,
            None    => write!(f, "None")?,
        };
        write!(f, ", kind: {:?}, name: {:?}, inode: {:?} }}",
               self.kind, self.name, self.inode)
    }
}

/// `Pwd` is the basis for traversing and modifying our filesystem. We separate it from
/// `FileSystem` because we occasionally create ephemeral `Pwd`s on the fly, and we don't want a
/// `Pwd`s `Drop` to invalidate our entire filesystem.
///
/// Recursive removes can delete the filesystem from underneath us - we can recursively remove a
/// parent directory. We need to invalidate the filesystem when that happens. Additionally, when a
/// filesystem drops, we need to delete everything under root. What happens if we recursively
/// removed root already? `Pwd`s `alive` covers both cases.
///
/// If our Pwd was removed, alive is false, and all operations fail. Any time we use root, we check
/// if Pwd is alive and, if it is not, we pointer compare root and `Pwd`s inner. If they are equal,
/// root is unusable (because alive being false means `Pwd`s inner has been dropped).
#[derive(Debug)]
struct Pwd {
    inner: Raw<Dirent>,
    alive: bool,
}

impl From<Raw<Dirent>> for Pwd {
    fn from(d: Raw<Dirent>) -> Pwd {
        Pwd {
            inner: d,
            alive: true,
        }
    }
}

/// `FileSystem` is a single in-memory filesystem that can be cloned and passed around safely. A
/// single `FileSystem` must be unique. On drop, the entire filesystem is deleted.
#[derive(Debug)]
struct FileSystem {
    // root exists for preemptive support for changing the current working directory. `cd` used to
    // exist, but was removed after adding symlink support. `root` held on to the original root
    // directory as needed.
    root: Raw<Dirent>,
    pwd:  Pwd,
}

impl Deref for FileSystem {
    type Target = Pwd;

    fn deref(&self) -> &Pwd {
        &self.pwd
    }
}

impl DerefMut for FileSystem {
    fn deref_mut(&mut self) -> &mut Pwd {
        &mut self.pwd
    }
}

impl Drop for FileSystem {
    fn drop(&mut self) {
        if !self.pwd.alive && Raw::ptr_eq(&self.root, &self.pwd.inner) {
            // It appears we have dropped ourself already.
            return;
        }

        let mut todo = Vec::new();
        todo.push(self.root);
        while let Some(elem) = todo.pop() {
            let rs = unsafe { Box::from_raw(elem.ptr()) };
            if let DeKind::Dir(ref d) = rs.kind {
                for child in d.values() {
                    todo.push(*child);
                }
            }
        }
    }
}

fn path_empty<P: AsRef<Path>>(path: P) -> bool {
    path.as_ref().as_os_str().is_empty()
}

// We claim that two filesystems are equal if they have the same structure, contents, and modes.
// This should only be used for testing.
impl PartialEq for FileSystem {
    fn eq(&self, other: &Self) -> bool {
        fn eq_at(l: Raw<Dirent>, r: Raw<Dirent>) -> bool {
            if l.inode.view() != r.inode.view() ||
                l.name != r.name {
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
                            Some(cr) => if !eq_at(*cl, *cr) {
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

        if !self.pwd.alive || !other.pwd.alive {
            panic!("invalid FileSystem PartialEq - both FileSystem's pwd must be alive!")
        }

        eq_at(self.root, other.root)
    }
}

impl Pwd {
    // up_path traverses up parent directories in a normalized path, erroring if we cannot cd into
    // (exec) the parent directory. Filesystem operations work relative to their canonicalized
    // path, even if we are inside a symlink. Changing directories does not change their atime.
    fn up_path(&self,
               parts: Parts)
               -> Result<(Raw<Dirent>, Vec<Part>)> {
        // up_path is the point of entry for every function in pwd. Conveniently, this also means
        // this is the only location we need to check if our filesystem has been removed from under
        // us via a remove_dir_all.
        if !self.alive {
            return Err(EINVAL());
        }
        // `up` is what we return: the dirent after traversing up all ParentDirs in `parts`.
        let mut up = self.inner;
        // If (normalized) parts begins at root, there are no ParentDirs. We do not need executable
        // privileges to return the root directory, even though in this code, we have to traverse
        // up to it.
        if parts.at_root {
            while let Some(parent) = up.parent {
                up = parent;
            }
            return Ok((up, parts.inner));
        }

        let mut parts_iter = parts.inner.into_iter().peekable();
        while parts_iter.peek()
                        .and_then(|part| if *part == Part::ParentDir { Some(()) } else { None })
                        .is_some() {
            parts_iter.next();
            if let Some(parent) = up.parent {
                if !parent.executable() {
                    return Err(EACCES());
                }
                up = parent;
            }
        }

        Ok((up, parts_iter.collect()))
    }

    // traverse goes up and down a path as necessary, returning the file system just before the
    // base of a path. Filesystem operations require executable perms to lookup all directories
    // along a path for an operation, but the base of the path may require more permissions.
    //
    // This returns an error if what we wanted to cd into is not a directory or is not executable.
    //
    // This traverses all symlinks when going down directories.
    fn traverse(&self,
                parts: Parts,
                level: &mut u8)
                -> Result<(Raw<Dirent>, Option<OsString>)> {
        if {*level += 1; *level} == 40 {
            return Err(ELOOP());
        }
        // First, we eat the parent directories. What remains will be purely normal paths.
        let (mut fs, parts) = self.up_path(parts)?;
        let mut parts_iter = parts.into_iter().peek2able();

        loop {
            let on = fs; // copy fs to not double borrow it
            match on.kind {
                DeKind::Dir(ref children) => {
                    // If there are not two more entries, we are just before the base. Return.
                    if !parts_iter.peek2().is_some() {
                        match parts_iter.next() {
                            Some(Part::Normal(base)) => return Ok((fs, Some(base))),
                            _ => return Ok((fs, None)),
                        }
                    }
                    // Change into the directory if we can and it exists.
                    if !fs.executable() {
                        return Err(EACCES());
                    }
                    fs = children.get(parts_iter
                                      .next()
                                      .expect("peek2 is Some, next is None")
                                      .as_normal()
                                      .expect("parts_iter should be Normal after up_path"))
                                  .cloned()
                                  .ok_or_else(ENOENT)?;
                }

                DeKind::Symlink(ref sl) => {
                    // We traverse the symlink before we can continue with parts_iter. We traverse
                    // _from_ its parent, and we must set fs to the traversed fs when it is done.
                    fs = fs.parent.expect("symlinks should always have a parent");
                    let (new_fs, may_base) = Pwd::from(fs).traverse(normalize(sl), level)?;
                    fs = new_fs;
                    match may_base {
                        Some(base) => {
                            let parts: Parts = Part::Normal(base).into();
                            // The returned fs traversed the symlink up to a directory's base.
                            // We need to push that to the front of our existing parts_iter.
                            //
                            // parts_iter is a Peek2able<PartsIntoIter>. We can't just blindly
                            // chain our new iterator (of one) into the existing parts_iter because
                            // the types are different.
                            //
                            // Since we don't really care about inefficiencies too much for
                            // symlinks ( only reasonable usage of a symlink in an in-memory
                            // filesystem would be for testing...), we'll just be inefficient.
                            parts_iter = parts.inner
                                              .into_iter()
                                              .chain(parts_iter)
                                              .collect::<Vec<Part>>()
                                              .into_iter()
                                              .peek2able();
                        },

                        None => {
                            if path_empty(sl) {
                                panic!("empty path in a symlink (should not be possible)");
                            }
                            // The symlink was either the root directory or entirely parent
                            // directories. We have already set fs above to the proper location.
                        }
                    }
                }

                _ => return Err(ENOTDIR()),
            }
        }
    }

    // This implements fs::canonicalize. It's a bit ugly, but we do what we gotta do. A filesystem
    // has no direct path down to a dirent, so we have to find where the end of the path is and
    // build the resulting path backwards to the root directory.
    //
    // This function is the _only_ reason Dirent's have `name`.
    fn canonicalize<P: AsRef<Path>>(&self, path: P, level: &mut u8) -> Result<PathBuf> {
        fn build_from_fs(mut fs: Raw<Dirent>) -> Result<PathBuf> {
            let mut rev = Vec::new();
            while !fs.name.is_empty() {
                rev.push(fs.name.clone());
                fs = fs.parent.expect("a non-root directory should have a parent, only root has no name");
            }
            rev.reverse();
            let mut pb = PathBuf::from("/");
            for p in rev {
                pb.push(p)
            }
            Ok(pb)
        }
        let (fs, may_base) = self.traverse(normalize(&path), level)?;
        let base = match may_base {
            Some(base) => base,
            None => {
                if path_empty(&path) {
                    return Err(ENOENT());
                }
                return build_from_fs(fs);
            }
        };

        if !fs.executable() {
            return Err(EACCES());
        }

        let parent = fs;
        match fs.kind.dir_ref().get(&base) {
            Some(child) => {
                if let DeKind::Symlink(ref sl) = child.kind {
                    if {*level += 1; *level} == 40 {
                        return Err(ELOOP());
                    }
                    return Pwd::from(parent).canonicalize(sl, level);
                }
                build_from_fs(*child)
            }
            None => Err(ENOENT()),
        }
    }

    // create_dir creates directories, failing if the directory exists and can_exist is false.
    fn create_dir<P: AsRef<Path>>(&self, path: P, mode: u32, can_exist: bool) -> Result<()> {
        let (mut fs, may_base) = self.traverse(normalize(&path), &mut 0)?;
        let base = match may_base {
            Some(base) => base,
            None => if path_empty(&path) {
                return Err(ENOENT());
            } else { // fs is at either root or a parent directory
                if can_exist {
                    return Ok(());
                }
                return Err(EEXIST());
            }
        };

        if !fs.changeable() {
            return Err(EACCES());
        }

        let parent = fs;
        match fs.kind.dir_mut().entry(base.clone()) {
            Entry::Occupied(o) => {
                // Symlinks are not followed for create_dir_all.
                if o.get().inode.view().ftyp.is_dir() && can_exist {
                    return Ok(())
                }
                Err(EEXIST())
            }
            Entry::Vacant(v) => {
                v.insert(Raw::from(Dirent {
                    parent: Some(parent),
                    kind:   DeKind::Dir(HashMap::new()),
                    name:   base,
                    inode:  Inode::new(mode, Ftyp::Dir, DIRLEN),
                }));
                Ok(())
            }
        }
    }

    fn create_dir_all<P: AsRef<Path>>(&self, path: P, mode: u32) -> Result<()> {
        let (_, parts) = self.up_path(normalize(&path))?;
        let mut path_buf = PathBuf::new();
        for part in parts {
            path_buf.push(part.into_normal().expect("parts_iter after up_path should only be Normal"));
            self.create_dir(&path_buf, mode, true)?;
        }
        Ok(())
    }

    fn hard_link<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()> {
        let (src_fs, src_may_base) = self.traverse(normalize(&src), &mut 0)?;
        let src_base = src_may_base.ok_or_else(EPERM)?; // I don't know why it is EPERM, but it is.

        // The error order appears to be:
        // - src dir must be executable
        // - dst must be dir (validated in traverse)
        // - dst must be executable
        // - src must exist
        // - dst file must not exist
        // - dst must be writable
        // - src must be file
        if !src_fs.executable() {
            return Err(EACCES());
        }

        let (mut dst_fs, dst_may_base) = self.traverse(normalize(&dst), &mut 0)?;
        let dst_base = dst_may_base.ok_or_else(EEXIST)?;

        if !dst_fs.executable() {
            return Err(EACCES());
        }
        let src_child = match src_fs.kind.dir_ref().get(&src_base) {
            Some(child) => child,
            None => return Err(ENOENT()),
        };
        if dst_fs.kind.dir_ref().get(&dst_base).is_some() {
            return Err(EEXIST());
        }
        if !dst_fs.writable() {
            return Err(EACCES());
        }

        let parent = dst_fs;
        match src_child.kind {
            DeKind::Dir(_) => Err(EPERM()),
            DeKind::Symlink(ref sl) => {
                dst_fs.kind
                      .dir_mut()
                      .insert(dst_base.clone(),
                              Raw::from(Dirent {
                                  parent: Some(parent),
                                  kind:   DeKind::Symlink(sl.clone()),
                                  name:   dst_base,
                                  inode:  src_child.inode.clone(),
                              }));
                Ok(())
            }
            DeKind::File(ref f) => {
                dst_fs.kind
                      .dir_mut()
                      .insert(dst_base.clone(),
                              Raw::from(Dirent {
                                  parent: Some(parent),
                                  kind:   DeKind::File(f.clone()),
                                  name:   dst_base,
                                  inode:  src_child.inode.clone(),
                              }));
                Ok(())
            }
        }
    }

    // symlink itself is an incredibly easy function to implement, so long as all the scaffolding
    // handling symlinks properly for directory traversal is already in place.
    fn symlink<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()> {
        let (mut dst_fs, dst_may_base) = self.traverse(normalize(&dst), &mut 0)?;
        let dst_base = dst_may_base.ok_or_else(EEXIST)?;

        if !dst_fs.changeable() {
            return Err(EACCES());
        }

        if dst_fs.kind.dir_ref().get(&dst_base).is_some() {
            return Err(EEXIST());
        }

        let sl = src.as_ref().to_owned();
        let len = sl.as_os_str().len();
        let parent = dst_fs;
        dst_fs.kind
              .dir_mut()
              .insert(dst_base.clone(),
                      Raw::from(Dirent {
                          parent: Some(parent),
                          kind:   DeKind::Symlink(sl),
                          name:   dst_base,
                          inode:  Inode::new(0o777, Ftyp::Symlink, len),
                      }));
        Ok(())
    }

    // I would have thought this required read permissions, but...
    //
    // "No permissions are required on the file itself, but—in the case of stat() ... execute
    // (search) permission is required on all of the directories in pathname that lead to the file.
    //
    // (see http://man7.org/linux/man-pages/man2/stat.2.html)
    //
    // This function is almost an exact duplicate of symlink_metadata. The only change comes in
    // when the base of the path if a symlink. Here, we recursively traverse it. I don't
    // particularaly want to figure out how to refactor the two to use the same code yet; my hunch
    // is that weaving through the recursion level through symlink_metadata and this and then
    // trying to parse the returned metadata and path name would be a bit convoluted.
    fn metadata<P: AsRef<Path>>(&self, path: P, level: &mut u8) -> Result<Metadata> {
        let (fs, may_base) = self.traverse(normalize(&path), level)?;
        let base = match may_base {
            Some(base) => base,
            None => if path_empty(path) {
                return Err(ENOENT());
            } else { // this is either the root dir or a parent dir
                return Ok(Metadata(fs.inode.view()));
            }
        };

        if !fs.executable() {
            return Err(EACCES());
        }

        let parent = fs;
        match fs.kind.dir_ref().get(&base) {
            Some(child) => {
                let meta = child.inode.view();
                if meta.ftyp.is_symlink() {
                    if {*level += 1; *level} == 40 {
                        return Err(ELOOP());
                    }
                    return Pwd::from(parent).metadata(child.kind.symlink_ref(), level);
                }
                Ok(Metadata(meta))
            }
            None => Err(ENOENT()),
        }
    }

    // read_dir implements, essentially, `ls`, traversing symlinks as necessary. We take the
    // orignial path that we called read_dir on; read_dir traverses symlinks based off the current
    // path, but returned DirEntry's are based off the original path.
    //
    // This function takes a recursion level as it may be recursive if the end of path is a symlink.
    fn read_dir<P: AsRef<Path>, Q: AsRef<Path>>(&self, og_path: Q, path: P, level: &mut u8) -> Result<ReadDir> {
        let (fs, may_base) = self.traverse(normalize(&path), level)?;
        let base = match may_base {
            Some(base) => base,
            None => if path_empty(&path) {
                return Err(ENOENT());
            } else { // path resolved to root or parent paths
                return ReadDir::new(&og_path, &*fs);
            }
        };

        if !fs.executable() {
            return Err(EACCES());
        }

        let parent = fs;
        match fs.kind.dir_ref().get(&base) {
            Some(child) => {
                // If the base of the path is a symlink, we ReadDir that.
                if let DeKind::Symlink(ref sl) = child.kind {
                    if {*level += 1; *level} == 40 {
                        return Err(ELOOP());
                    }
                    return Pwd::from(parent).read_dir(og_path, sl, level);
                }
                // Otherwise we ReadDir whatever this is - ReadDir::new handles ENOTDIR.
                ReadDir::new(&og_path, &*child)
            },
            None => Err(ENOENT()),
        }
    }

    fn read_link<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        let (fs, may_base) = self.traverse(normalize(&path), &mut 0)?;
        let base = may_base.ok_or_else(||
            if path_empty(&path) {
                ENOENT()
            } else {
                EINVAL()
            })?;

        if !fs.executable() {
            return Err(EACCES());
        }
        match fs.kind.dir_ref().get(&base) {
            Some(child) => match child.kind {
                DeKind::Symlink(ref sl) => Ok(sl.clone()),
                _ => Err(EINVAL()),
            },
            None => Err(ENOENT()),
        }
    }

    fn remove<P: AsRef<Path>>(&self, path: P, kind: FileType) -> Result<()> {
        let (mut fs, may_base) = self.traverse(normalize(&path), &mut 0)?;
        let base = may_base.ok_or_else(||
            if path_empty(&path) {
                ENOENT()
            } else {
                ENOTEMPTY()
            })?;


        // We need to make sure that the FileType being requested for removal matches the FileType
        // of the directory. Scope this check so child drops before we mutate it.
        {
            if !fs.changeable() {
                return Err(EACCES());
            }
            let child = fs.kind
                          .dir_ref()
                          .get(&base)
                          .ok_or_else(ENOENT)?;

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

        // Because I'm a masochist, we have to clean up the memory behind our filesystem outselves.
        let removed = fs.kind
                        .dir_mut()
                        .remove(&base)
                        .expect("remove logic checking existence is wrong");
        // We cannot remove a directory underneath pwd, so we are fine.
        unsafe { Box::from_raw(removed.ptr()); }
        Ok(())
    }
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.remove(path, FileType(Ftyp::File))
    }
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.remove(path, FileType(Ftyp::Dir))
    }

    fn remove_dir_all<P: AsRef<Path>>(&mut self, path: P) -> Result<()> {
        // Unfortunately, with remove_dir _all, we can actually remove the dirent we are on. This
        // is valid. We need to support it. But, because I'm doing things unsafely, we have to be
        // careful to not use free memory after this is over.
        //
        // We will do this by comparing every deleted dirent to our pwd, and, if one is our pwd, we
        // will invalidate ourself.
        fn maybe_kill_self(pwd: &mut Pwd, removed: &Raw<Dirent>) {
            if pwd.alive && Raw::ptr_eq(removed, &pwd.inner) {
                pwd.alive = false;
            }
        }
        // Rust's remove_dir_all is actually very weak (weaker than rm -r). Rust relies on read_dir
        // to recurse, which requires `ls`. Standard linux is able to remove empty directories with
        // only write and execute privileges. This code attempts to mimic what Rust will do.
        fn recursive_remove(pwd: &mut Pwd, mut fs: Raw<Dirent>) -> Result<()> {
            let accessible = fs.rremovable();
            if let DeKind::Dir(ref mut children) = fs.kind { // symlinks & files are simply removed
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

                    let mut err = Ok(());
                    for &(child_name, child) in &child_names {
                        match recursive_remove(pwd, *child) {
                            Ok(_) => deleted.push(child_name.clone()),
                            Err(e) => { err = Err(e); break; },
                        }
                    }
                    err
                };
                // We have to actually remove everything we successfully recursively "deleted".
                for child_name in deleted {
                    let removed = children.remove(&child_name)
                                          .expect("deleted has child_name not in child map");
                    maybe_kill_self(pwd, &removed);
                    unsafe { Box::from_raw(removed.ptr()); } // free the memory
                }
                res?
            }
            Ok(())
        }


        let (mut fs, may_base) = self.traverse(normalize(&path), &mut 0)?;
        match may_base {
            Some(base) => { // removing a non-root path
                if !fs.changeable() {
                    return Err(EACCES());
                }
                if let Entry::Occupied(child) = fs.kind.dir_mut().entry(base) {
                    recursive_remove(self, *child.get())?;
                    maybe_kill_self(self, child.get());
                    unsafe { Box::from_raw(child.remove().ptr()); }
                }
            }
            None => { // removing either a direct parent directory or everything under root.
                if path_empty(&path) {
                    return Err(ENOENT());
                }
                recursive_remove(self, fs)?;
                maybe_kill_self(self, &fs);
                unsafe { Box::from_raw(fs.ptr()); }
            }
        }
        Ok(())
    }

    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        let (mut old_fs, old_may_base) = self.traverse(normalize(&from), &mut 0)?;
        let old_base = old_may_base.ok_or_else(||
            if path_empty(&from) {
                ENOENT()
            } else if old_fs.parent.is_some() {
                EBUSY() // renaming through parent directories returns EBUSY
            } else {
                // I really don't want to support this, nor manually test what can happen.
                Error::new(ErrorKind::Other, "rename of root unimplemented")
            })?;
        let (mut new_fs, new_may_base) = self.traverse(normalize(&to), &mut 0)?;
        let new_base = new_may_base.ok_or_else(||
            if path_empty(&to) {
                ENOENT()
            } else if new_fs.parent.is_some() {
                EBUSY()
            } else {
                EEXIST()
            })?;

        if Raw::ptr_eq(&old_fs, &new_fs) && old_base == new_base {
            return Ok(());
        }

        // The error order appears to be:
        // - both dirs must be executable
        // - file must exist
        // - both dirs must be writable
        // - files must be the same type (and for directories, empty)

        if !old_fs.executable() || !new_fs.executable() {
            return Err(EACCES());
        }

        // Rust's rename is strong, but also annoying, in that it can rename a directory to a
        // directory if that directory is empty. We could make the code elegant, but this will do.
        let (old_exist, old_is_dir) =
            match old_fs.kind.dir_ref().get(&old_base) {
                Some(child) => (true, child.is_dir()),
                None => (false, false),
            };

        if !old_exist {
            return Err(ENOENT());
        }

        if !old_fs.writable() || !new_fs.writable() {
            return Err(EACCES());
        }

        let (new_exist, new_is_dir, new_is_empty) =
            match new_fs.kind.dir_ref().get(&new_base) {
                Some(child) => match child.kind {
                    DeKind::Dir(ref children) => (true, true, children.is_empty()),
                    _ => (true, false, false),
                },
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

        let mut renamed = old_fs.kind.dir_mut().remove(&old_base)
                            .expect("logic verifying dirent existence is wrong");
        renamed.name = new_base.clone();
        let mut inode = renamed.inode.write();
        inode.times.update(MODIFIED|ACCESSED|CREATED);
        new_fs.kind.dir_mut().insert(new_base, renamed);
        Ok(())
    }

    // set_permissions implements chmod, traversing symlinks as necessary.
    //
    // This function takes a recursion level as it may be recursive if the end of path is a symlink.
    fn set_permissions<P: AsRef<Path>>(&self, path: P, perms: Permissions, level: &mut u8) -> Result<()> {
        let (mut fs, may_base) = self.traverse(normalize(&path), level)?;
        let base = match may_base {
            Some(base) => base,
            None => if path_empty(&path) {
                return Err(ENOENT());
            } else {
                // Symlinks are always 0o777. If traverse returns no base, path resolved to
                // either the root directory or a parent directory - we can set perms.
                fs.inode.write().perms = perms;
                return Ok(());
            }
        };
        if !fs.executable() {
            return Err(EACCES());
        }
        let parent = fs;
        match fs.kind.dir_ref().get(&base) {
            Some(child) => {
                // set_permissions on symlinks changes what they link to, so we recurse.
                if let DeKind::Symlink(ref sl) = child.kind {
                    if {*level += 1; *level} == 40 {
                        return Err(ELOOP());
                    }
                    return Pwd::from(parent).set_permissions(sl, perms, level);
                }
                let mut child = *child; // copy out of the borrow
                child.inode.write().perms = perms;
                Ok(())
            }
            None => Err(ENOENT()),
        }
    }

    fn symlink_metadata<P: AsRef<Path>>(&self, path: P) -> Result<Metadata> {
        let (fs, may_base) = self.traverse(normalize(&path), &mut 0)?;
        let base = match may_base {
            Some(base) => base,
            None => if path_empty(path) {
                return Err(ENOENT());
            } else {
                return Ok(Metadata(fs.inode.view())); // either the root dir or a parent dir
            }
        };

        if !fs.executable() {
            return Err(EACCES());
        }

        match fs.kind.dir_ref().get(&base) {
            Some(child) => Ok(Metadata(child.inode.view())),
            None => Err(ENOENT()),
        }
    }

    // open has to take the master filesystem (FS) because File itself can call set_permissions.
    // There is probably an avenue to clean this up.
    fn open<P: AsRef<Path>>(&self,
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
        let (mut fs, may_base) = self.traverse(normalize(&path), level)?;
        let base = match may_base {
            Some(base) => base,
            None => if path_empty(&path) {
                return Err(ENOENT());
            } else { // root or parent directories only (both of which,
                     // being dirs, fail immediately in open_existing)
                return Self::open_existing(&fs, &options);
            }
        };

        if !fs.executable() {
            return Err(EACCES());
        }
        // If the file exists, open it.
        let parent = fs;
        if let Some(child) = fs.kind.dir_ref().get(&base) {
            if let DeKind::Symlink(ref sl) = child.kind {
                if {*level += 1; *level} == 40 {
                    return Err(ELOOP());
                }
                return Pwd::from(parent).open(sl, &options, level);
            }
            return Self::open_existing(child, &options);
        }

        // From here down we worry about creating a new file.
        if !options.create {
            return Err(ENOENT());
        }
        if !fs.writable() {
            return Err(EACCES());
        }

        let file = Arc::new(RwLock::new(RawFile { // backing "inode" file
            data:  Vec::new(),
            inode: Inode::new(options.mode, Ftyp::File, 0),
        }));
        let child = Raw::from(Dirent {
            parent: Some(fs),
            kind:   DeKind::File(file.clone()),
            name:   base.clone(),
            inode:  file.write().inode.clone(),
        });
        fs.kind.dir_mut().insert(base, child);
        Ok(File { // file view
            read:   options.read,
            write:  options.write,
            append: options.append,

            cursor: Arc::new(Mutex::new(FileCursor {
                file: file,
                at:   0,
            })),
        })
    }

    // `open_existing` opens known existing file with the given options, returning an error if the
    // file cannot be opened with those options.
    fn open_existing(fs: &Raw<Dirent>, options: &OpenOptions) -> Result<File> {
        if options.excl {
            return Err(EEXIST());
        }

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

        let file = fs.kind.file_ref().clone();
        {
            let mut raw_file = file.write();
            if options.trunc {
                raw_file.data = Vec::new();
            }
            raw_file.inode.write().times.update(ACCESSED);
        }
        Ok(File {
            read:   read,
            write:  write,
            append: options.append,
            cursor: Arc::new(Mutex::new(FileCursor {
                file: file,
                at:   0,
            })),
        })
    }
}

#[cfg(test)]
mod test {
    use std::ffi::OsString;
    use std::io::Error;
    use std::sync::mpsc;
    use std::thread;

    use fs::{DirEntry as DirEntryTrait, File, GenFS, OpenOptions};
    use unix_ext::*;
    use super::*;

    impl PartialEq for FS {
        fn eq(&self, other: &Self) -> bool {
            *self.0.lock() == *other.0.lock()
        }
    }

    fn errs_eq(l: Error, r: Error) -> bool {
        l.raw_os_error() == r.raw_os_error()
    }
    fn ref_errs_eq(l: &Error, r: &Error) -> bool {
        l.raw_os_error() == r.raw_os_error()
    }

    #[test]
    fn equal() {
        // First, we prove our filesystem comparison operations work.
        let mut exp_root = Raw::from(Dirent {
            parent: None,
            kind:   DeKind::Dir(HashMap::new()),
            name:   OsString::from(""),
            inode:  Inode::new(0, Ftyp::Dir, DIRLEN),
        });

        let exp = FS(Arc::new(Mutex::new(FileSystem {
                root: exp_root,
                pwd:  Pwd::from(exp_root),
            })));
        {
            let parent = exp_root;
            let ref mut dir = exp_root.kind.dir_mut();
            dir.insert(OsString::from("lolz"), Raw::from(Dirent {
                parent: Some(parent),
                kind:   DeKind::Dir(HashMap::new()),
                name:   OsString::from("lolz"),
                inode:  Inode::new(0o666, Ftyp::Dir, DIRLEN),
            }));
            let file_inode = Inode::new(0o334, Ftyp::File, 3);
            dir.insert(OsString::from("f"), Raw::from(Dirent {
                parent: Some(parent),
                kind:   DeKind::File(Arc::new(RwLock::new(RawFile{
                    data:  vec![1, 2, 3],
                    inode: file_inode.clone(),
                }))),
                name:   OsString::from("f"),
                inode:  file_inode,
            }));
            dir.insert(OsString::from("sl"), Raw::from(Dirent {
                parent: Some(parent),
                kind:   DeKind::Symlink(String::from(".././zzz").into()),
                name:   OsString::from("sl"),
                inode:  Inode::new(0o777, Ftyp::Symlink, 8),
            }));
        }

        let fs = FS::with_mode(0o777);
        assert!(fs.new_dirbuilder().mode(0o666).create("lolz").is_ok());
        let mut f = fs.new_openopts().mode(0o334).write(true).create_new(true).open("f").unwrap();
        assert!(f.write(vec![1, 2, 3].as_slice()).is_ok());
        assert!(fs.symlink(".././zzz", "sl").is_ok());
        assert!(fs.set_permissions("/", Permissions::from_mode(0)).is_ok());
        assert!(fs == exp);
        // TODO this test proves that equality works, but does not prove that inequality is
        // correct. While I have verified it, every piece of the above fs could be changed
        // to prove it via a test.
    }

    #[test]
    fn create_dir() {
        // We just proved that file system comparisons work. Let's build a slightly more
        // complicated filesystem and then prove create_dir works.
        let mut exp_root = Raw::from(Dirent {
            parent: None,
            kind:   DeKind::Dir(HashMap::new()),
            name:   OsString::from(""),
            inode:  Inode::new(0o300, Ftyp::Dir, DIRLEN),
        });
        let exp = FS(Arc::new(Mutex::new(FileSystem {
                root: exp_root,
                pwd:  Pwd::from(exp_root),
            })));

        {
            let parent = exp_root;
            let children = exp_root.kind.dir_mut();
            children.insert(OsString::from("a"), Raw::from(Dirent {
                parent: Some(parent),
                kind:   DeKind::Dir(HashMap::new()),
                name:   OsString::from("a"),
                inode:  Inode::new(0o500, Ftyp::Dir, DIRLEN), // r-x: cannot create subiles
            }));
            children.insert(OsString::from("b"), Raw::from(Dirent {
                parent: Some(parent),
                kind:   DeKind::Dir(HashMap::new()),
                name:   OsString::from("b"),
                inode:  Inode::new(0o600, Ftyp::Dir, DIRLEN), // rw-: cannot exec to create subfiles
            }));
            let mut child = Raw::from(Dirent {
                parent: Some(parent),
                kind:   DeKind::Dir(HashMap::new()),
                name:   OsString::from("c"),
                inode:  Inode::new(0o300, Ftyp::Dir, DIRLEN), // _wx: all we need
            });
            {
                let parent = child;
                let child_children = child.kind.dir_mut();
                child_children.insert(OsString::from("d"), Raw::from(Dirent {
                    parent: Some(parent),
                    kind:   DeKind::Dir(HashMap::new()),
                    name:   OsString::from("d"),
                    inode:  Inode::new(0o777, Ftyp::Dir, DIRLEN),
                }));
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
        assert!(fs.new_dirbuilder().mode(0o777).create("c/d").is_ok());
        assert!(fs == exp);
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

        assert!(fs.set_permissions("a/b", Permissions::from_mode(0o600)).is_ok());
        assert!(errs_eq(fs.new_dirbuilder().mode(0o100).create("a/b/z").unwrap_err(),
                        EACCES()));
        assert!(exp.set_permissions("a/b", Permissions::from_mode(0o600)).is_ok());
        assert!(fs == exp);
    }

    #[test]
    fn open() {
        // We proved open worked in the first test, so let's test OpenOptions combinations and how
        // they interact with directories that have poor perms.
        let fs = FS::with_mode(0o700);
        assert!(fs.new_dirbuilder().mode(0o100).create("unwrite").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("unexec/subdir").is_ok());
        assert!(fs.new_dirbuilder().mode(0o300).recursive(true).create("okdir").is_ok());
        assert!(fs.set_permissions("unexec", Permissions::from_mode(0o200)).is_ok());
        assert!(errs_eq(fs.new_openopts().write(true).open("").unwrap_err(), ENOENT()));

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
                        on, &res_err, &exp_err);
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
        test_open(on(), &fs, t, f, f, f, f, f, 0o700, "okdir", Some(Error::new(ErrorKind::Other, "")));

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

        assert!(errs_eq(fs.remove_dir("a").unwrap_err(), ENOTEMPTY()));
        assert!(errs_eq(fs.remove_dir("a/c/z").unwrap_err(), ENOTDIR()));
        assert!(errs_eq(fs.remove_dir("a/z").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.remove_dir("a/d").unwrap_err(), ENOTEMPTY()));

        assert!(fs.remove_file("a/c").is_ok());
        assert!(errs_eq(fs.remove_dir("../../unexec/subdir").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.remove_dir("../a/d").unwrap_err(), ENOTEMPTY()));
        assert!(fs.remove_dir("../a/d/e/./").is_ok());

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

        let fs = FS::new();
        assert!(fs.remove_dir_all(".").is_ok());
        assert!(errs_eq(fs.canonicalize("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.copy("a", "b").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.create_dir("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.create_dir_all("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.hard_link("a", "b").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.metadata("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.read_dir("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.read_link("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.remove_dir("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.remove_dir_all("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.remove_file("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.rename("a", "b").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.set_permissions("a", Permissions::from_mode(0)).unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.symlink_metadata("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.symlink("a", "b").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.open_file("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.create_file("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.new_openopts().write(true).create(true).open("a").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.new_dirbuilder().create("a").unwrap_err(), EINVAL()));
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

        fn de_eq(this: DirEntry, other: DirEntry) -> bool {
            this.dir == other.dir &&
                this.base == other.base &&
                this.inode == other.inode
        }

        let mut reader = fs.read_dir("a/b").unwrap();
        assert!(de_eq(reader.next().unwrap().unwrap(), DirEntry {
            dir:   PathBuf::from("a/b"),
            base:  OsString::from("c"),
            inode: Inode::new(0o700, Ftyp::Dir, DIRLEN),
        }));
        assert!(de_eq(reader.next().unwrap().unwrap(), DirEntry {
            dir:   PathBuf::from("a/b"),
            base:  OsString::from("d"),
            inode: Inode::new(0o300, Ftyp::Dir, DIRLEN),
        }));
        let next = reader.next().unwrap().unwrap();
        assert_eq!(next.path(), PathBuf::from("a/b/f"));
        assert_eq!(next.file_name(), OsString::from("f"));
        let meta = next.metadata().unwrap();
        assert!(meta.0 == Inode::new(0, Ftyp::File, 0).view());
        let next = reader.next().unwrap().unwrap();
        assert_eq!(next.path(), PathBuf::from("a/b/z"));
        assert_eq!(next.file_name(), OsString::from("z"));
        assert!(next.metadata().unwrap().0 == Inode::new(0o100, Ftyp::Dir, DIRLEN).view());
        assert!(reader.next().is_none());
    }

    #[test]
    fn raw_file() {
        let mut raw_file = RawFile {
            data: Vec::new(),
            inode: Inode::new(0, Ftyp::File, 0),
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

        assert_eq!(raw_file.inode.read().length, 6);

        assert_eq!(raw_file.write_at(10, &slice[..1]).unwrap(), 1);
        assert_eq!(raw_file.data.as_slice(), &[1, 1, 2, 3, 4, 5, 0, 0, 0, 0, 1]);

        let mut output = [0u8; 2];
        assert_eq!(raw_file.read_at(9, &mut output).unwrap(), 2);
        assert_eq!(&output, &[0, 1]);

        assert_eq!(raw_file.read_at(8, &mut output).unwrap(), 2);
        assert_eq!(&output, &[0, 0]);

        assert_eq!(raw_file.inode.read().length, 11);
    }

    #[test]
    fn usage() {
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
    fn thread() {
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

    #[test]
    fn hard_link() {
        let fs = FS::with_mode(0o300);
        assert!(fs.new_openopts().mode(0o600).create(true).write(true).open("f").is_ok());
        assert!(fs.symlink("f", "sl").is_ok());

        assert!(fs.new_dirbuilder().mode(0).create("a").is_ok()); // EACCES
        assert!(fs.create_file("b").is_ok()); // ENOTDIR
        assert!(fs.new_dirbuilder().mode(0).create("c").is_ok()); // EACCES

        assert!(fs.create_dir("d").is_ok());
        assert!(fs.create_file("d/f").is_ok()); // EEXIST

        assert!(fs.new_dirbuilder().mode(0o100).create("e").is_ok()); // EACCES

        assert!(errs_eq(fs.hard_link("a/f", "z").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.hard_link("f", "b/f").unwrap_err(), ENOTDIR()));
        assert!(errs_eq(fs.hard_link("f", "c/f").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.hard_link("z", "q").unwrap_err(),   ENOENT()));
        assert!(errs_eq(fs.hard_link("f", "d/f").unwrap_err(), EEXIST()));
        assert!(errs_eq(fs.hard_link("f", "e/f").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.hard_link("a", "z").unwrap_err(),   EPERM()));

        assert!(fs.hard_link("f", "z").is_ok());
        assert!(fs.hard_link("sl", "ls").is_ok());

        let mut f = fs.new_openopts().write(true).open("f").unwrap();
        assert_eq!(f.write(vec![1, 2, 3].as_slice()).unwrap(), 3);

        // While we are here, let's test copy quickly.
        assert_eq!(fs.copy("f", "cpy").unwrap(), 3);
        assert_eq!(fs.metadata("cpy").unwrap().permissions().mode(), 0o600);
        assert_eq!(fs.copy("q", "d").unwrap_err().kind(), ErrorKind::InvalidInput);
        assert_eq!(fs.copy("d", "d").unwrap_err().kind(), ErrorKind::InvalidInput);

        let mut z = fs.new_openopts().write(true).append(true).open("z").unwrap(); // through hard link
        {
            let cursor = z.cursor.lock();
            let file = cursor.file.read();
            assert_eq!(file.data.as_slice(), &[1, 2, 3]);
        }
        assert_eq!(z.write(vec![1, 2, 3].as_slice()).unwrap(), 3);


        {
            let f = fs.open_file("ls").unwrap(); // through linked (copied) symlink to f
            let cursor = f.cursor.lock();
            let file = cursor.file.read();
            assert_eq!(file.data.as_slice(), &[1, 2, 3, 1, 2, 3]);
        }

        {
            let f = fs.open_file("cpy").unwrap(); // ensure our copied file is still normal
            let cursor = f.cursor.lock();
            let file = cursor.file.read();
            assert_eq!(file.data.as_slice(), &[1, 2, 3]);
        }

        {
            let cursor = f.cursor.lock(); // re-check the initial f
            let file = cursor.file.read();
            assert_eq!(file.data.as_slice(), &[1, 2, 3, 1, 2, 3]);
        }
    }

    #[test]
    fn symlink() {
        // We proved, in our first test, that creating symlinks works. Let's test everything
        // through symlinks.
        let fs = FS::with_mode(0o300);
        let exp = FS::with_mode(0o300);
        assert!(fs.symlink("hello", "sl").is_ok());
        assert!(exp.symlink("hello", "sl").is_ok());
        assert!(fs.symlink("goodbye", "hello").is_ok());
        assert!(exp.symlink("goodbye", "hello").is_ok());
        assert!(fs.symlink("unexec", "u").is_ok());
        assert!(exp.symlink("unexec", "u").is_ok());

        assert!(fs.create_dir("goodbye").is_ok());
        assert!(fs.symlink(".././a", "goodbye/sl").is_ok());
        assert!(fs.create_dir("a").is_ok());
        assert!(fs.create_dir("sl/sl/b").is_ok());
        assert!(fs.create_file("sl/sl/f").is_ok());
        assert!(exp.create_dir_all("a/b").is_ok());
        assert!(exp.create_file("a/f").is_ok());
        assert!(exp.create_dir("goodbye").is_ok());
        assert!(exp.symlink(".././a", "goodbye/sl").is_ok());
        assert!(fs == exp);

        assert!(fs.new_dirbuilder().mode(0).create("unexec").is_ok());
        assert!(exp.new_dirbuilder().mode(0).create("unexec").is_ok());

        // Throw in our canonicalize testing.
        assert_eq!(fs.canonicalize("../././/sl/.//sl/b/../").unwrap(), PathBuf::from("/a"));
        assert_eq!(fs.canonicalize("../").unwrap(), PathBuf::from("/"));
        assert!(errs_eq(fs.canonicalize("").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.canonicalize("a/d/z").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.canonicalize("sl/sl/z").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.canonicalize("unexec/z").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.canonicalize("u/z").unwrap_err(), EACCES()));

        assert!(fs.remove_dir_all("sl/sl/b/c").is_ok());
        assert!(exp.remove_dir_all("a/b/c").is_ok());
        assert!(fs == exp);

        assert!(fs.remove_dir("sl/sl/b").is_ok());
        assert!(exp.remove_dir("a/b").is_ok());
        assert!(fs == exp);

        // Throw in our read_link testing.
        assert_eq!(fs.read_link("sl").unwrap(), PathBuf::from("hello"));
        assert_eq!(fs.read_link("sl/sl").unwrap(), PathBuf::from(".././a"));
        assert!(errs_eq(fs.read_link("").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.read_link("..").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.read_link("unexec/a").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.read_link("u/a").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.read_link("goodbye").unwrap_err(), EINVAL()));
        assert!(errs_eq(fs.read_link("goodbye/d").unwrap_err(), ENOENT()));

        // Metadata through symlinks...
        assert_eq!(fs.metadata("sl").unwrap().0, Inode::new(0o777, Ftyp::Dir, DIRLEN).view());
        assert_eq!(fs.metadata("sl/sl").unwrap().0, Inode::new(0o777, Ftyp::Dir, DIRLEN).view());
        assert_eq!(fs.metadata("sl/sl/f").unwrap().0, Inode::new(0o666, Ftyp::File, 0).view());
        assert!(errs_eq(fs.metadata("u/f").unwrap_err(), EACCES()));

        // All of symlink_metadata...
        assert_eq!(fs.symlink_metadata("sl").unwrap().0, Inode::new(0o777, Ftyp::Symlink, 5).view());
        assert_eq!(fs.symlink_metadata("sl/sl").unwrap().0, Inode::new(0o777, Ftyp::Symlink, 6).view());
        assert_eq!(fs.symlink_metadata("..").unwrap().0, Inode::new(0o300, Ftyp::Dir, DIRLEN).view());
        assert_eq!(fs.symlink_metadata("unexec").unwrap().0, Inode::new(0, Ftyp::Dir, DIRLEN).view());
        assert_eq!(fs.symlink_metadata("a/f").unwrap().0, Inode::new(0o666, Ftyp::File, 0).view());
        assert_eq!(fs.symlink_metadata("sl/sl/f").unwrap().0, Inode::new(0o666, Ftyp::File, 0).view());
        assert!(errs_eq(fs.symlink_metadata("unexec/a").unwrap_err(), EACCES()));
        assert!(errs_eq(fs.symlink_metadata("q").unwrap_err(), ENOENT()));
        assert!(errs_eq(fs.symlink_metadata("").unwrap_err(), ENOENT()));

        // Set perms...
        assert!(fs.set_permissions("sl/sl", Permissions::from_mode(0o700)).is_ok());
        assert!(exp.set_permissions("a", Permissions::from_mode(0o700)).is_ok());
        assert!(fs == exp);

        // Read_dir...
        let mut read = fs.read_dir("sl/sl").unwrap();
        assert_eq!(read.next().unwrap().unwrap().path(), PathBuf::from("sl/sl/f"));
        assert!(read.next().is_none());

        // Remove_file (tested via exp fs) and rename (via fs)...
        assert!(fs.rename("sl/sl", "sl/longsl").is_ok());
        assert!(exp.remove_file("sl/sl").is_ok());
        assert!(exp.symlink(".././a", "sl/longsl").is_ok());
        assert!(fs == exp);

        // ELOOP
        assert!(fs.symlink("z", "z").is_ok());
        assert!(errs_eq(fs.metadata("z/z").unwrap_err(), ELOOP())); // via traverse
        assert!(errs_eq(fs.canonicalize("z").unwrap_err(), ELOOP()));
        assert!(errs_eq(fs.metadata("z").unwrap_err(), ELOOP()));
        assert!(errs_eq(fs.metadata("z").unwrap_err(), ELOOP()));
        assert!(errs_eq(fs.read_dir("z").unwrap_err(), ELOOP()));
        assert!(errs_eq(fs.set_permissions("z", Permissions::from_mode(0)).unwrap_err(), ELOOP()));
        assert!(errs_eq(fs.open_file("z").unwrap_err(), ELOOP()));

        assert!(exp.symlink("z", "z").is_ok());
        assert!(fs == exp);

        // Open is tested in hard_link
    }
}
