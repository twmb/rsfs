//! This module provides basic generic types for a filesystem.

use std::ffi::OsString;
use std::fmt::Debug;
use std::hash::Hash;
use std::io::{Read, Seek, Write};
use std::io::Result;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

/// A builder used to create directories.
///
/// This trait replaces [`std::fs::DirBuilder`] with the exception of its `new` function. To create
/// a new `DirBuilder`, use [`GenFS::new_dirbuilder`].
///
/// [`std::fs::DirBuilder`]: https://doc.rust-lang.org/std/fs/struct.DirBuilder.html
/// [`GenFS::new_dirbuilder`]: trait.GenFS.html#tymethod.new_dirbuilder
pub trait DirBuilder: Debug {
    /// Indicates that directories should be opened recursively, creating directories if they do
    /// not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    ///
    /// let fs = FS::new();
    /// let mut builder = fs.new_dirbuilder();
    /// builder.recursive(true);
    /// ```
    fn recursive(&mut self, recursive: bool) -> &mut Self;
    /// Creates the directory specified by `path`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    ///
    /// let path = "/foo/bar/baz";
    /// let fs = FS::new();
    /// fs.new_dirbuilder()
    ///   .recursive(true)
    ///   .create(path).unwrap();
    ///
    /// assert!(fs.metadata(path).unwrap().is_dir());
    /// ```
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()>;
}

/// Entries returned by the iterator returned from [`read_dir`].
///
/// `DirEntry` represents an entry inside a directory on a filesystem that can be inspected to
/// learn about the entry.
///
/// [`read_dir`]: trait.GenFS.html#tymethod.read_dir
pub trait DirEntry: Debug {
    /// The `Metadata` type in the same module implementing this trait.
    type Metadata: Metadata;
    /// The `FileType` type in the same module implementing this trait.
    type FileType: FileType;

    /// Returns the full path to the file or directory this entry represents.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// for entry in fs.read_dir(".")? {
    ///     let entry = entry?;
    ///     println!("{:?}", entry.path());
    /// }
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// This prints output like:
    ///
    /// ```text
    /// "./foo.txt"
    /// "./README.md"
    /// ```
    fn path(&self) -> PathBuf;
    /// Returns metadata for the file this entry represents.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// for entry in fs.read_dir(".")? {
    ///     let entry = entry?;
    ///     println!("{:?}: {:?}", entry.path(), entry.metadata()?.permissions());
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn metadata(&self) -> Result<Self::Metadata>;
    /// Returns the file type for what this entry points at.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// for entry in fs.read_dir(".")? {
    ///     let entry = entry?;
    ///     println!("{:?}: {:?}", entry.path(), entry.file_type()?);
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn file_type(&self) -> Result<Self::FileType>;
    /// Returns the base name of the file or directory this entry represents.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// for entry in fs.read_dir(".")? {
    ///     println!("{:?}", entry?.file_name());
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn file_name(&self) -> OsString;
}

/// A reference to an open file on the filesystem.
///
/// An instance of `File` can be read or written to depending on the options it was opened with.
/// Files also implement `Seek` to alter the logical cursor position of the internal file.
///
/// Files are automatically closed when they go out of scope.
///
/// # Examples
///
/// Create a new file and write bytes to it:
///
/// ```
/// use rsfs::*;
/// use rsfs::mem::FS;
/// use std::io::prelude::*;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
///
/// let mut file = fs.create_file("foo.txt")?;
/// file.write_all(b"Hello, original std::fs examples!")?;
/// # Ok(())
/// # }
/// ```
///
/// Read the contents of a file into a `String`:
///
///
/// ```
/// use rsfs::*;
/// use rsfs::mem::FS;
/// use std::io::prelude::*;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
///
/// let mut file = fs.open_file("foo.txt")?;
/// let mut contents = String::new();
/// file.read_to_string(&mut contents)?;
/// assert_eq!(contents, "Hello, original std::fs examples!");
/// # Ok(())
/// # }
/// ```
///
/// It can be more efficient to read the contents of a file with a buffered
/// [`Read`]er. This can be accomplished with [`BufReader<R>`]:
///
/// ```
/// use rsfs::*;
/// use rsfs::mem::FS;
/// use std::io::BufReader;
/// use std::io::prelude::*;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
///
/// let file = fs.open_file("foo.txt")?;
/// let mut buf_reader = BufReader::new(file);
/// let mut contents = String::new();
/// buf_reader.read_to_string(&mut contents)?;
/// assert_eq!(contents, "Hello, world!");
/// # Ok(())
/// # }
/// ```
///
/// [`Read`]: ../io/trait.Read.html
/// [`BufReader<R>`]: ../io/struct.BufReader.html
pub trait File: Debug + Read + Seek + Write + Sized {
    /// The `Metadata` type in the same module implementing this trait.
    type Metadata: Metadata;
    /// The `Permissions` type in the same module implementing this trait.
    type Permissions: Permissions;

    /// Attempts to sync all OS-internal metadata to the filesystem.
    ///
    /// This function will attempt to ensure all in-memory data reaches the filesystem before
    /// returning.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// use std::io::prelude::*;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let mut f = fs.create_file("foo.txt")?;
    /// f.write_all(b"Hello, original std::fs examples!")?;
    ///
    /// f.sync_all()?;
    /// # Ok(())
    /// # }
    /// ```
    fn sync_all(&self) -> Result<()>;
    /// This function is similar to [`sync_all`], except that it may not synchronize metadata to
    /// the filesystem.
    ///
    /// This is intended for uses that must synchronize content, but do not need the metadata. The
    /// goal of this method is to reduce filesystem operations, but note that some platforms may
    /// implement this as [`sync_all`].
    ///
    /// [`sync_all`]: trait.File.html#tymethod.sync_all
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// use std::io::prelude::*;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let mut f = fs.create_file("foo.txt")?;
    /// f.write_all(b"Hello, original std::fs examples!")?;
    ///
    /// f.sync_data()?;
    /// # Ok(())
    /// # }
    /// ```
    fn sync_data(&self) -> Result<()>;
    /// Truncates or extends the underlying file, updating the size of this file to become `size`.
    ///
    /// If `size` is less than the file's current size, the file will be shrunk. If greater, the
    /// file will be zero extended to `size`.
    ///
    /// # Errors
    ///
    /// This function will return an error if the file is not opened for writing.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let mut f = fs.create_file("foo.txt")?;
    /// f.set_len(10)?;
    /// # Ok(())
    /// # }
    /// ```
    fn set_len(&self, size: u64) -> Result<()>;
    /// Queries information about the underlying file.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.open_file("foo.txt")?;
    /// let metadata = file.metadata()?;
    /// # Ok(())
    /// # }
    /// ```
    fn metadata(&self) -> Result<Self::Metadata>;
    /// Generates a new, independently owned handle to the underlying file.
    ///
    /// The returned `File` is a reference to the same file cursor that this `File` reference. Both
    /// handles will read and write with the same file cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.open_file("foo.txt")?;
    /// let file_copy = file.try_clone()?;
    /// # Ok(())
    /// # }
    /// ```
    fn try_clone(&self) -> Result<Self>;
    /// Changes the permissions on the underlying file.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.open_file("foo.txt")?;
    /// let mut perms = file.metadata()?.permissions();
    /// perms.set_readonly(true);
    /// file.set_permissions(perms)?;
    /// # Ok(())
    /// # }
    /// ```
    fn set_permissions(&self, perm: Self::Permissions) -> Result<()>;
}

/// Returned from [`Metadata::file_type`], this trait represents the type of a file.
///
/// [`Metadata::file_type`]: trait.Metadata.html#tymethod.file_type
pub trait FileType: Copy + Clone + PartialEq + Eq + Hash + Debug {
    /// Returns whether this file type is a directory.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    /// let file_type = metadata.file_type();
    ///
    /// assert_eq!(file_type.is_dir(), false);
    /// # Ok(())
    /// # }
    /// ```
    fn is_dir(&self) -> bool;
    /// Returns whether this file type is a file.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    /// let file_type = metadata.file_type();
    ///
    /// assert_eq!(file_type.is_file(), true);
    /// # Ok(())
    /// # }
    /// ```
    fn is_file(&self) -> bool;
    /// Returns whether this file type is a symlink.
    ///
    /// This will only ever be true if the underlying [`Metadata`] type is retrieved with `GenFS`s
    /// [`symlink_metadata`] method.
    ///
    /// [`Metadata`]: trait.Metadata.html
    /// [`symlink_metadata`]: trait.GenFS.html#tymethod.symlink_metadata
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    /// let file_type = metadata.file_type();
    ///
    /// assert_eq!(file_type.is_symlink(), false);
    /// # Ok(())
    /// # }
    /// ```
    fn is_symlink(&self) -> bool;
}

/// Metadata information about a file.
///
/// This trait is returned from `GenFS`s [`metadata`] or [`symlink_metadata`] methods and
/// represents known metadata information about a file at the instant this trait is instantiated.
///
/// [`metadata`]: trait.GenFS.html#tymethod.metadata
/// [`symlink_metadata`]: trait.GenFS.html#tymethod.symlink_metadata
pub trait Metadata: Clone + Debug  {
    /// The `Permissions` type in the same module implementing this trait.
    type Permissions: Permissions;
    /// The `FileType` type in the same module implementing this trait.
    type FileType: FileType;

    /// Returns the file type for this metadata.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// println!("{:?}", metadata.file_type());
    /// # Ok(())
    /// # }
    /// ```
    fn file_type(&self) -> Self::FileType;
    /// Returns whether this metadata is for a directory.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// assert!(!metadata.is_dir());
    /// # Ok(())
    /// # }
    /// ```
    fn is_dir(&self) -> bool;
    /// Returns whether this metadata is for a file.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// assert!(metadata.is_file());
    /// # Ok(())
    /// # }
    /// ```
    fn is_file(&self) -> bool;
    /// Returns the size, in bytes, of the file this metadata is for.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// assert_eq!(0, metadata.len());
    /// # Ok(())
    /// # }
    /// ```
    fn len(&self) -> u64;
    /// Returns whether the file is empty. This defaults to checking `len() == 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// assert!(metadata.is_empty());
    /// # Ok(())
    /// # }
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Returns the permissions of the file this metadata is for.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// assert!(!metadata.permissions().readonly());
    /// # Ok(())
    /// # }
    /// ```
    fn permissions(&self) -> Self::Permissions;
    /// Returns the last modification time listed in this metadata.
    ///
    /// # Errors
    ///
    /// This method will return `Err` on systems where it is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// if let Ok(time) = metadata.modified() {
    ///     println!("{:?}", time);
    /// } else {
    ///     println!("Not supported on this platform");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn modified(&self) -> Result<SystemTime>;
    /// Returns the last access time listed in this metadata.
    ///
    /// # Errors
    ///
    /// This method will return `Err` on systems where it is unavailable.
    ///
    /// Note that most systems will not keep a access times up to date.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// if let Ok(time) = metadata.accessed() {
    ///     println!("{:?}", time);
    /// } else {
    ///     println!("Not supported on this platform");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn accessed(&self) -> Result<SystemTime>;
    /// Returns the creation time listed in this metadata.
    ///
    /// # Errors
    ///
    /// This method will return `Err` on systems where it is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let metadata = fs.metadata("foo.txt")?;
    ///
    /// if let Ok(time) = metadata.created() {
    ///     println!("{:?}", time);
    /// } else {
    ///     println!("Not supported on this platform");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn created(&self) -> Result<SystemTime>;
}

/// Options and flags which can be used to configure how a file is opened.
///
/// This trait replaces [`std::fs::OpenOption`] with the exception of its `new` function. To create
/// a new `OpenOptions`, use [`GenFS::new_openopts`].
///
/// [`std::fs::OpenOptions`]: https://doc.rust-lang.org/std/fs/struct.OpenOptions.html
/// [`GenFS::new_openopts`]: trait.GenFS.html#tymethod.new_openopts
///
/// # Examples
///
/// Opening a file to read:
///
///
/// ```
/// use rsfs::*;
/// use rsfs::mem::FS;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
///
/// let file = fs.new_openopts().read(true).open("foo.txt")?;
/// # Ok(())
/// # }
/// ```
///
/// Opening a file for reading and writing and creating it if it does not exist:
///
///
/// ```
/// use rsfs::*;
/// use rsfs::mem::FS;
/// # fn foo() -> std::io::Result<()> {
/// let fs = FS::new();
///
/// let file = fs.new_openopts()
///              .read(true)
///              .write(true)
///              .create(true)
///              .open("foo.txt")?;
/// # Ok(())
/// # }
/// ```
pub trait OpenOptions: Clone + Debug {
    /// The `File` type in the module implementing this trait.
    type File: File;

    /// Sets the option for read access.
    ///
    /// This option, when true, indicates a file should be `read`-able if opened. 
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.new_openopts().read(true).open("foo.txt")?;
    /// # Ok(())
    /// # }
    fn read(&mut self, read: bool) -> &mut Self;
    /// Sets the option for write access.
    ///
    /// This option, when true, indicates a file should be `write`-able if opened. 
    ///
    /// If the file already exists, write calls will overwrite existing file contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.new_openopts().write(true).open("foo.txt")?;
    /// # Ok(())
    /// # }
    fn write(&mut self, write: bool) -> &mut Self;
    /// Sets the option for append mode.
    ///
    /// This option, when true, means the file will always append to the current end of the file as
    /// opposed to overwriting existing contents.
    ///
    /// Note that `.append(true)` implies `.write(true)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.new_openopts().append(true).open("foo.txt")?;
    /// # Ok(())
    /// # }
    fn append(&mut self, append: bool) -> &mut Self;
    /// Sets the option for truncating an existing file.
    ///
    /// The file must be opened with write access for truncate to work.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.new_openopts().write(true).truncate(true).open("foo.txt")?;
    /// # Ok(())
    /// # }
    fn truncate(&mut self, truncate: bool) -> &mut Self;
    /// Sets the option to create the file if it does not exist.
    ///
    /// In order for a file to be created, `write` or `append` must also be used with this option.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.new_openopts().write(true).create(true).open("foo.txt")?;
    /// # Ok(())
    /// # }
    fn create(&mut self, create: bool) -> &mut Self;
    /// Sets the option to always create a new file.
    ///
    /// This option indicates whether a new file must be created, ensuring the file cannot exist
    /// already.
    ///
    /// In order for a file to be created, `write` or `append` must also be used with this option.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.new_openopts().write(true).create_new(true).open("foo.txt")?;
    /// # Ok(())
    /// # }
    fn create_new(&mut self, create_new: bool) -> &mut Self;
    /// Opens a file at `path` with options specified by `self`.
    ///
    /// # Errors
    ///
    /// This function will return an error under a number of different circumstances, including but
    /// not limited to:
    ///
    /// * Opening a file that does not exist without setting create or create_new.
    /// * Attempting to open a file with access that the user lacks permissions for
    /// * Filesystem-level errors (full disk, etc)
    /// * Invalid combinations of open options (truncate without write access, no access mode set,
    /// etc)
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.new_openopts().open("foo.txt")?;
    /// # Ok(())
    /// # }
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File>;
}

/// Representation of the various permissions on a file.
///
/// This trait only requires [`readonly`] and [`set_readonly`], which are the only two "cross
/// platform" functions provided in `std::fs`. However, the [`unix_ext`] module has a useful
/// [`PermissionsExt`] trait to complement this one.
///
/// [`readonly`]: trait.Permissions.html#tymethod.readonly
/// [`set_readonly`]: trait.Permissions.html#tymethod.set_readonly
/// [`unix_ext`]: unix_ext/index.html
/// [`PermissionsExt`]: unix_ext/trait.PermissionsExt.html
pub trait Permissions: Clone + PartialEq + Eq + Debug {
    /// Returns whether these permissions have readonly set.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.create_file("foo.txt")?;
    /// let metadata = file.metadata()?;
    ///
    /// assert_eq!(false, metadata.permissions().readonly());
    /// # Ok(())
    /// # }
    /// ```
    fn readonly(&self) -> bool;
    /// Modifies the readonly fly for these permissions.
    ///
    /// This does not modify the filesystem. To modify the filesystem, use the filesystem's
    /// [`set_permissions`] function.
    ///
    /// [`set_permissions`]: trait.GenFS.html#tymethod.set_permissions
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let file = fs.create_file("foo.txt")?;
    /// let metadata = file.metadata()?;
    /// let mut permissions = metadata.permissions();
    ///
    /// permissions.set_readonly(true);
    ///
    /// // filesystem doesn't change
    /// assert_eq!(false, metadata.permissions().readonly());
    ///
    /// // just this particular `permissions`.
    /// assert_eq!(true, permissions.readonly());
    /// # Ok(())
    /// # }
    /// ```
    fn set_readonly(&mut self, readonly: bool);
}

/// The single filesystem underpinning all filesystem operations.
///
/// This trait intends to be a near drop in replacement for most uses of [`std::fs`]. As with
/// [`std::fs`], all methods in this trait are cross-platform. Extra platform specific
/// functionality can be found in the extension traits of `rsfs::$platform_ext`.
///
/// [`std::fs`]: https://doc.rust-lang.org/std/fs/
///
/// # Examples
///
/// The normal, disk backed filesystem:
///
/// ```
/// use rsfs::*;
///
/// let fs = rsfs::disk::FS;
/// ```
///
/// An in-memory filesystem with Unix extensions:
///
/// ```
/// use rsfs::*;
/// use rsfs::unix_ext::*;
/// use rsfs::mem::FS;
///
/// let fs = FS::with_mode(0o300);
/// ```
pub trait GenFS: Send + Sync {
    /// The `DirBuilder` type in the same module implementing this trait.
    type DirBuilder: DirBuilder;
    /// The `DirEntry` type in the same module implementing this trait.
    type DirEntry: DirEntry;
    /// The `File` type in the same module implementing this trait.
    type File: File;
    /// The `Metadata` type in the same module implementing this trait.
    type Metadata: Metadata;
    /// The `OpenOptions` type in the same module implementing this trait.
    type OpenOptions: OpenOptions;
    /// The `Permissions` type in the same module implementing this trait.
    type Permissions: Permissions;
    /// The `ReadDir` type in the same module implementing this trait.
    type ReadDir: Iterator<Item = Result<Self::DirEntry>> + Debug;

    /// Returns the canonical form of a path with all intermediate components normalized and
    /// symbolic links resolved.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `path` does not exist
    /// * `A component in `path` is not a directory
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let path = fs.canonicalize("../a/../foo.txt")?;
    /// # Ok(())
    /// # }
    /// ```
    fn canonicalize<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf>;

    /// Copies the contents of one file to another. This function will also copy the permission bits
    /// of the original file to the destination file.
    ///
    /// Note that this function will *overwrite* the contents of `to` and, if `from` and `to` are
    /// the same file, the file will likely be truncated by this function.
    ///
    /// On success, the total number of bytes copied is returned.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `from` is not a file
    /// * `from` does not exist
    /// * User lacks permissions to access `from` or write `to`
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.copy("foo.txt", "bar.txt")?; // Copy foo.txt to bar.txt
    /// # Ok(())
    /// # }
    /// ```
    fn copy<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<u64>;

    /// Creates a new, empty directory at the provided path.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `path` exists
    /// * User lacks permissions to create a directory at `path`
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.create_dir("/some/dir")?;
    /// # Ok(())
    /// # }
    /// ```
    fn create_dir<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Recursively creates a directory and all its parent components if they are missing.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * User lacks permissions to create any directories in `path`
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.create_dir_all("/some/dir")?;
    /// # Ok(())
    /// # }
    /// ```
    fn create_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Creates a new hard link on the filesystem.
    ///
    /// The `dst` path will be a link pointing to the `src` path.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * The `src` path is not a file or does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.hard_link("a.txt", "b.txt")?; // Hard link a.txt to b.txt
    /// # Ok(())
    /// # }
    /// ```
    fn hard_link<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()>;

    /// Returns metadata information of the file or directory at path.
    ///
    /// This function will traverse symbolic links to query a directory or file.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * User lacks permissions to call `metadata` on `path`
    /// * `path` does not exist
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let attr = fs.metadata("/some/file/path.txt")?;
    /// // inspect attr...
    /// # Ok(())
    /// # }
    /// ```
    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata>;

    /// Returns an iterator over entries within a directory.
    ///
    /// The iterator yields instances of [`io::Result`]`::`[`DirEntry`]. New errors may be
    /// encountered after the iterator is initially constructed.
    ///
    /// [`io::Result`]: https://doc.rust-lang.org/std/io/type.Result.html
    /// [`DirEntry`]: trait.DirEntry.html
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `path` does not exist
    /// * `path` is not a directory
    /// * User lacks permissions to read the directory at `path`
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// for entry in fs.read_dir("/")? {
    ///     println!("{:?}", entry?.path());
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<Self::ReadDir>;

    /// Reads a symbolic link, returning the entry the link points to.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `path` does not exist
    /// * `path` is not a symbolic link
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let path = fs.read_link("foo")?;
    /// # Ok(())
    /// # }
    /// ```
    fn read_link<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf>;

    /// Removes an existing, empty directory.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `path` is not a directory
    /// * User lacks permissions to remove the directory at `path`
    /// * The directory is not empty
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.remove_dir("/some/dir")?;
    /// # Ok(())
    /// # }
    /// ```
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Removes a directory at path after removing all of its contents.
    ///
    /// # Errors
    ///
    /// See [`remove_dir`] and [`remove_file`].
    ///
    /// [`remove_dir`]: trait.GenFS.html#tymethod.remove_dir
    /// [`remove_file`]: trait.GenFS.html#tymethod.remove_file
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.remove_dir_all("/some/dir")?;
    /// # Ok(())
    /// # }
    /// ```
    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Removes a file from the filesystem.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `path` is a directory
    /// * User lacks permissions to remove the file at `path`
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.remove_file("a.txt")?;
    /// # Ok(())
    /// # }
    /// ```
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Renames a file or directory at `from` to `to`, replacing `to` if it exists.
    ///
    /// # Platform-specific behavior
    ///
    /// Behavior differs between Unix and Windows. On Unix, if `from` is a directory, `to` must
    /// also be an (empty) directory. If `from` is not a directory, `to` must not be a directory.
    /// On Windows, `from` can be anything, but `to` must not be a directory.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `from` does not exist
    /// * User lacks permissions to rename `from`
    /// * `from` and `to` are on separate filesystems
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.rename("a.txt", "b.txt")?;
    /// # Ok(())
    /// # }
    /// ```
    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()>;

    /// Changes the permissions of a file or directory.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * `path` does not exist
    /// * User lacks permissions to changes the attributes of the entry at `path`
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::unix_ext::*;
    /// use rsfs::mem::{FS, Permissions};
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// fs.set_permissions("foo.pem", Permissions::from_mode(0o400))?;
    /// # Ok(())
    /// # }
    /// ```
    fn set_permissions<P: AsRef<Path>>(&self, path: P, perm: Self::Permissions) -> Result<()>;

    /// Query the metadata about a file without following symlinks.
    ///
    /// # Errors
    ///
    /// While there may be more error cases, this function will error in the following cases:
    ///
    /// * User lacks permissions to call `symlink_metadata` on `path`
    /// * `path` does not exist
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let attr = fs.symlink_metadata("/some/file/path.txt")?;
    /// // inspect attr...
    /// # Ok(())
    /// # }
    /// ```
    fn symlink_metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata>;

    /// Returns a new OpenOptions for a file for this filesytem.
    ///
    /// This method replaces [`std::fs::OpenOptions::new()`], which now needs to be a part of this
    /// trait to ensure any new file belongs to the `GenFS` that created the `OpenOptions`.
    ///
    /// [`std::fs::OpenOptions::new()`]: https://doc.rust-lang.org/std/fs/struct.OpenOptions.html#method.new
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let mut options = fs.new_openopts();
    /// let file = options.read(true).open("foo.txt")?;
    /// # Ok(())
    /// # }
    /// ```
    fn new_openopts(&self) -> Self::OpenOptions;
    /// Returns a new DirBuilder for a directory for this filesystem.
    ///
    /// This method replaces [`std::fs::DirBuilder::new()`], which now needs to be a part of this
    /// trait to ensure any new directory belongs to the `GenFS` that created the `DirBuilder`.
    ///
    /// [`std::fs::DirBuilder::new()`]: https://doc.rust-lang.org/std/fs/struct.DirBuilder.html#method.new
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let mut builder = fs.new_dirbuilder();
    /// # Ok(())
    /// # }
    /// ```
    fn new_dirbuilder(&self) -> Self::DirBuilder;

    /// Opens a file in read-only mode.
    ///
    /// This method replaces [`std::fs::File::open()`], which now needs to be a part of this trait
    /// to ensure that the opened file belongs to the calling `GenFS`.
    ///
    /// See [`OpenOptions::open`] for more details.
    ///
    /// [`std::fs::File::open()`]: https://doc.rust-lang.org/std/fs/struct.File.html#method.open
    /// [`OpenOptions::open`]: trait.OpenOptions.html#tymethod.open
    ///
    /// # Errors
    ///
    /// This function will return an error if `path` does not exist. Other errors may be returned
    /// according to [`OpenOptions::open`].
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let mut file = fs.open_file("foo.txt")?;
    /// # Ok(())
    /// # }
    /// ```
    fn open_file<P: AsRef<Path>>(&self, path: P) -> Result<Self::File>;
    /// Opens a file in write-only mode.
    ///
    /// This method replaces [`std::fs::File::create()`], which now needs to be a part of this trait
    /// to ensure that the created file belongs to the calling `GenFS`.
    ///
    /// This function will create a file if it does not exist and truncate it if it does.
    ///
    /// See [`OpenOptions::create`] for more details.
    ///
    /// [`std::fs::File::create()`]: https://doc.rust-lang.org/std/fs/struct.File.html#method.create
    /// [`OpenOptions::create`]: trait.OpenOptions.html#tymethod.create
    ///
    /// # Examples
    ///
    /// ```
    /// use rsfs::*;
    /// use rsfs::mem::FS;
    /// # fn foo() -> std::io::Result<()> {
    /// let fs = FS::new();
    ///
    /// let mut file = fs.create_file("foo.txt")?;
    /// # Ok(())
    /// # }
    /// ```
    fn create_file<P: AsRef<Path>>(&self, path: P) -> Result<Self::File>;
}
