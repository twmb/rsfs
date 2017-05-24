//! A zero cost wrapper around [`std::fs`].
//!
//! The [`FS`] struct is an empty struct. All methods on it use `std::fs` functions. The intent of
//! this module is to set the filesystem you use to `rsfs::disk::FS` in `main.rs` and to set the
//! filesystem to `rsfs::mem::test::FS` or something else in your tests.
//!
//! [`std::fs`]: https://doc.rust-lang.org/std/fs/
//! [`FS`]: struct.FS.html
//!
//! # Examples
//!
//! ```
//! use rsfs::*;
//! use rsfs::unix_ext::*;
//!
//! let fs = rsfs::disk::FS;
//!
//! let meta = fs.metadata("/").unwrap();
//! assert!(meta.is_dir());
//! assert_eq!(meta.permissions().mode(), 0o755);
//! ```

use std::ffi::OsString;
use std::fs as rs_fs;
use std::io::{Read, Result, Seek, SeekFrom, Write};
use std::os::unix::fs::{DirBuilderExt, FileExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use fs;

#[cfg(unix)]
use unix_ext;

/// A builder used to create directories in various manners.
///
/// This builder is a single element tuple containing a [`std::fs::DirBuilder`] that implements [`rsfs::DirBuilder`] and supports [unix extensions].
///
/// [`std::fs::DirBuilder`]: https://doc.rust-lang.org/std/fs/struct.DirBuilder.html
/// [`rsfs::DirBuilder`]: ../trait.DirBuilder.html
/// [unix extensions]: ../unix_ext/trait.DirBuilderExt.html
///
/// # Examples
/// 
/// ```
/// # use rsfs::*;
/// # fn foo() -> std::io::Result<()> {
/// let fs = rsfs::disk::FS;
/// let db = fs.new_dirbuilder();
/// db.create("dir")?;
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct DirBuilder(rs_fs::DirBuilder);

impl fs::DirBuilder for DirBuilder {
    fn recursive(&mut self, recursive: bool) -> &mut Self {
        self.0.recursive(recursive); self
    }
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.0.create(path)
    }
}

#[cfg(unix)]
impl unix_ext::DirBuilderExt for DirBuilder {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.0.mode(mode); self
    }
}

/// Entries returned by the [`ReadDir`] iterator.
///
/// An instance of `DirEntry` implements [`rsfs::DirEntry`] and represents an entry inside a
/// directory on the in memory filesystem. This struct is a single element tuple containing a
/// [`std::fs::DirEntry`].
///
/// [`ReadDir`]: struct.ReadDir.html
/// [`rsfs::DirEntry`]: ../trait.DirEntry.html
/// [`std::fs::DirEntry`]: https://doc.rust-lang.org/std/fs/struct.DirEntry.html
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # fn foo() -> std::io::Result<()> {
/// let fs = rsfs::disk::FS;
/// for entry in fs.read_dir(".")? {
///     let entry = entry?;
///     println!("{:?}: {:?}", entry.path(), entry.metadata()?.permissions());
/// }
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct DirEntry(rs_fs::DirEntry);

impl fs::DirEntry for DirEntry {
    type Metadata = Metadata;
    type FileType = FileType;

    fn path(&self) -> PathBuf {
        self.0.path()
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        self.0.metadata().map(Metadata)
    }
    fn file_type(&self) -> Result<Self::FileType> {
        self.0.file_type().map(FileType)
    }
    fn file_name(&self) -> OsString {
        self.0.file_name()
    }
}

/// Returned from [`Metadata::file_type`], this structure represents the type of a file.
///
/// This structure is a single element tuple containing a [`std::fs::FileType`] that implements [`rsfs::FileType`].
///
/// [`Metadata::file_type`]: ../trait.Metadata.html#tymethod.file_type
/// [`std::fs::FileType`]: https://doc.rust-lang.org/std/fs/struct.FileType.html
/// [`rsfs::FileType`]: ../trait.FileType.html
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # fn foo() -> std::io::Result<()> {
/// let fs = rsfs::disk::FS;
/// let f = fs.create_file("f")?;
/// assert!(fs.metadata("f")?.file_type().is_file());
/// # Ok(())
/// # }
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct FileType(rs_fs::FileType);

impl fs::FileType for FileType {
    fn is_dir(&self) -> bool {
        self.0.is_dir()
    }
    fn is_file(&self) -> bool {
        self.0.is_file()
    }
    fn is_symlink(&self) -> bool {
        self.0.is_symlink()
    }
}

/// A view into a file on the filesystem.
///
/// An instance of `File` can be read or written to depending on the options it was opened with.
/// Files also implement `Seek` to alter the logical cursor position of the internal file.
///
/// This struct is a single element tuple containing a [`std::fs::File`] that implements
/// [`rsfs::File`] and has [unix extensions].
///
/// [`std::fs::File`]: https://doc.rust-lang.org/std/fs/struct.File.html
/// [`rsfs::File`]: ../trait.File.html
/// [unix extensions]: ../unix_ext/trait.FileExt.html
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # use std::io::Write;
/// # fn foo() -> std::io::Result<()> {
/// let fs = rsfs::disk::FS;
/// let mut f = fs.create_file("f")?;
/// assert_eq!(f.write(&[1, 2, 3])?, 3);
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct File(rs_fs::File);

impl fs::File for File {
    type Metadata = Metadata;
    type Permissions = Permissions;

    fn sync_all(&self) -> Result<()> {
        self.0.sync_all()
    }
    fn sync_data(&self) -> Result<()> {
        self.0.sync_data()
    }
    fn set_len(&self, size: u64) -> Result<()> {
        self.0.set_len(size)
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        self.0.metadata().map(Metadata)
    }
    fn try_clone(&self) -> Result<Self> {
        self.0.try_clone().map(File)
    }
    fn set_permissions(&self, perm: Self::Permissions) -> Result<()> {
        self.0.set_permissions(perm.0)
    }
}

impl Read for File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.0.read(buf)
    }
}
impl Write for File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.0.write(buf)
    }
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}
impl Seek for File {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        self.0.seek(pos)
    }
}

impl<'a> Read for &'a File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        (&self.0).read(buf)
    }
}
impl<'a> Write for &'a File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        (&self.0).write(buf)
    }
    fn flush(&mut self) -> Result<()> {
        Ok(())
    }
}
impl<'a> Seek for &'a File {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        (&self.0).seek(pos)
    }
}

impl unix_ext::FileExt for File {
    fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize> {
        self.0.read_at(buf, offset)
    }
    fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize> {
        self.0.write_at(buf, offset)
    }
}

/// Metadata information about a file.
///
/// This structure, a single element tuple containing a [`std::fs::Metadata`] that implements
/// [`rsfs::Metadata`], is returned from the [`metadata`] or [`symlink_metadata`] methods and
/// represents known metadata information about a file at the instant in time this structure is
/// instantiated.
///
/// [`std::fs::Metadata`]: https://doc.rust-lang.org/std/fs/struct.Metadata.html
/// [`rsfs::Metadata`]: ../trait.Metadata.html
/// [`metadata`]: ../trait.GenFS.html#tymethod.metadata
/// [`symlink_metadata`]: ../trait.GenFS.html#tymethod.symlink_metadata
///
/// # Examples
///
/// ```
/// # use rsfs::*;
/// # fn foo() -> std::io::Result<()> {
/// let fs = rsfs::disk::FS;
/// fs.create_file("f")?;
/// println!("{:?}", fs.metadata("f")?);
/// # Ok(())
/// # }
#[derive(Clone, Debug)]
pub struct Metadata(rs_fs::Metadata);

impl fs::Metadata for Metadata {
    type Permissions = Permissions;
    type FileType = FileType;

    fn file_type(&self) -> Self::FileType {
        FileType(self.0.file_type())
    }
    fn is_dir(&self) -> bool {
        self.0.is_dir()
    }
    fn is_file(&self) -> bool {
        self.0.is_file()
    }
    fn len(&self) -> u64 {
        self.0.len()
    }
    fn permissions(&self) -> Self::Permissions {
        Permissions(self.0.permissions())
    }
    fn modified(&self) -> Result<SystemTime> {
        self.0.modified()
    }
    fn accessed(&self) -> Result<SystemTime> {
        self.0.accessed()
    }
    fn created(&self) -> Result<SystemTime> {
        self.0.created()
    }
}

/// Options and flags which can be used to configure how a file is opened.
///
/// This builder, created from `GenFS`s [`new_openopts`], exposes the ability to configure how a
/// [`File`] is opened and what operations are permitted on the open file. `GenFS`s [`open_file`]
/// and [`create_file`] methods are aliases for commonly used options with this builder.
///
/// This builder is a single element tuple containing a [`std::fs::OpenOptions`] that implements
/// [`rsfs::OpenOptions`] and supports [unix extensions].
///
/// [`new_openopts`]: ../trait.GenFS.html#tymethod.new_openopts
/// [`open_file`]: ../trait.GenFS.html#tymethod.open_file
/// [`create_file`]: ../trait.GenFS.html#tymethod.create_file
/// [`std::fs::OpenOptions`]: https://doc.rust-lang.org/std/fs/struct.OpenOptions.html
/// [`rsfs::OpenOptions`]: ../trait.OpenOptions.html
/// [unix extensions]: ../unix_ext/trait.OpenOptionsExt.html
///
/// # Examples
///
/// Opening a file to read:
///
/// ```
/// # use rsfs::*;
/// # fn foo() -> std::io::Result<()> {
/// # let fs = rsfs::disk::FS;
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
/// # fn foo() -> std::io::Result<()> {
/// # let fs = rsfs::disk::FS;
/// let mut f = fs.new_openopts()
///               .read(true)
///               .write(true)
///               .create(true)
///               .open("f")?;
/// # Ok(())
/// # }
/// ```
#[derive(Clone, Debug)]
pub struct OpenOptions(rs_fs::OpenOptions);

impl fs::OpenOptions for OpenOptions {
    type File = File;

    fn read(&mut self, read: bool) -> &mut Self {
        self.0.read(read); self
    }
    fn write(&mut self, write: bool) -> &mut Self {
        self.0.write(write); self
    }
    fn append(&mut self, append: bool) -> &mut Self {
        self.0.append(append); self
    }
    fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.0.truncate(truncate); self
    }
    fn create(&mut self, create: bool) -> &mut Self {
        self.0.create(create); self
    }
    fn create_new(&mut self, create_new: bool) -> &mut Self {
        self.0.create_new(create_new); self
    }
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        self.0.open(path).map(File)
    }
}

#[cfg(unix)]
impl unix_ext::OpenOptionsExt for OpenOptions {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.0.mode(mode); self
    }
    fn custom_flags(&mut self, flags: i32) -> &mut Self {
        self.0.custom_flags(flags); self
    }
}

/// Representation of the various permissions on a file.
///
/// This struct is a single element tuple containing a [`std::fs::Permissions`] that implements
/// [`rsfs::Permissions`] and has [unix extensions].
///
/// [`std::fs::Permissions`]: https://doc.rust-lang.org/std/fs/struct.Permissions.html
/// [`rsfs::Permissions`]: ../trait.Permissions.html
/// [unix extensions]: ../unix_ext/trait.PermissionsExt.html
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
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Permissions(rs_fs::Permissions);

impl fs::Permissions for Permissions {
    fn readonly(&self) -> bool {
        self.0.readonly()
    }
    fn set_readonly(&mut self, readonly: bool) {
        self.0.set_readonly(readonly)
    }
}

#[cfg(unix)]
impl unix_ext::PermissionsExt for Permissions {
    fn mode(&self) -> u32 {
        self.0.mode()
    }
    fn set_mode(&mut self, mode: u32) {
        self.0.set_mode(mode)
    }
    fn from_mode(mode: u32) -> Self {
        Permissions(rs_fs::Permissions::from_mode(mode))
    }
}

/// Iterator over entries in a directory.
///
/// This is returned from the [`read_dir`] method of `GenFS` and yields instances of
/// `io::Result<DirEntry>`. Through a [`DirEntry`], information about contents of a directory can
/// be learned.
///
/// This struct is as ingle element tuple containing a [`std::fs::ReadDir`].
///
/// [`read_dir`]: struct.FS.html#method.read_dir
/// [`DirEntry`]: struct.DirEntry.html
/// [`std::fs::ReadDir`]: https://doc.rust-lang.org/std/fs/struct.ReadDir.html
#[derive(Debug)]
pub struct ReadDir(rs_fs::ReadDir);

impl Iterator for ReadDir {
    type Item = Result<DirEntry>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|res_dirent| res_dirent.map(DirEntry))
    }
}

/// An empty struct that satisfies [`rsfs::FS`] by calling [`std::fs`] functions.
///
/// Because this is an empty struct, it is inherently thread safe and copyable. The power of using
/// `rsfs` comes from the ability to choose what filesystem you want to use where: your main can
/// use a disk backed filesystem, but your tests can use a test filesystem with injected errors.
///
/// Alternatively, the in-memory filesystem could suit your needs without forcing you to use disk.
///
/// [`rsfs::FS`]: ../trait.FS.html
/// [`std::fs`]: https://doc.rust-lang.org/std/fs/
///
/// # Examples
/// 
/// ```
/// use rsfs::*;
///
/// let fs = rsfs::disk::FS;
/// ```
#[derive(Copy, Clone, Debug)]
pub struct FS;

impl fs::GenFS for FS {
    type DirBuilder = DirBuilder;
    type DirEntry = DirEntry;
    type File = File;
    type Metadata = Metadata;
    type OpenOptions = OpenOptions;
    type Permissions = Permissions;
    type ReadDir = ReadDir;

    fn canonicalize<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        rs_fs::canonicalize(path)
    }
    fn copy<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<u64> {
        rs_fs::copy(from, to)
    }
    fn create_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        rs_fs::create_dir(path)
    }
    fn create_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        rs_fs::create_dir_all(path)
    }
    fn hard_link<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()> {
        rs_fs::hard_link(src, dst)
    }
    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata> {
        rs_fs::metadata(path).map(Metadata)
    }
    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<Self::ReadDir> {
        rs_fs::read_dir(path).map(ReadDir)
    }
    fn read_link<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        rs_fs::read_link(path)
    }
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        rs_fs::remove_dir(path)
    }
    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        rs_fs::remove_dir_all(path)
    }
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        rs_fs::remove_file(path)
    }
    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        rs_fs::rename(from, to)
    }
    fn set_permissions<P: AsRef<Path>>(&self, path: P, perm: Self::Permissions) -> Result<()> {
        rs_fs::set_permissions(path, perm.0)
    }
    fn symlink_metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata> {
        rs_fs::symlink_metadata(path).map(Metadata)
    }
    fn new_openopts(&self) -> Self::OpenOptions {
        OpenOptions(rs_fs::OpenOptions::new())
    }
    fn new_dirbuilder(&self) -> Self::DirBuilder {
        DirBuilder(rs_fs::DirBuilder::new())
    }
    fn open_file<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        rs_fs::File::open(path).map(File)
    }
    fn create_file<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        rs_fs::File::create(path).map(File)
    }
}

#[cfg(unix)]
impl unix_ext::GenFSExt for FS {
    fn symlink<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()> {
        ::std::os::unix::fs::symlink(src, dst)
    }
}
