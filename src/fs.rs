//! This module provides basic generic types for a filesystem.

use std::ffi::OsString;
use std::io::{Read, Seek, Write};
use std::io::Result;
use std::path::{Path, PathBuf};

/// A builder used to create directories.
///
/// This trait replaces [`std::fs::DirBuilder`] with the exception of its `new` function. To create
/// a new `DirBuilder`, use [`GenFS::new_dirbuilder`].
///
/// [`std::fs::DirBuilder`]: https://doc.rust-lang.org/std/fs/struct.DirBuilder.html
/// [`GenFS::new_dirbuilder`]: trait.GenFS.html#tymethod.new_dirbuilder
pub trait DirBuilder {
    /// Indicates that directories should be opened recursively, creating directories if they do
    /// not exist.
    fn recursive(&mut self, recursive: bool) -> &mut Self;
    /// Creates the directory specified by `path`.
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()>;
}

/// Entries returned by the iterator returned from `read_dir`.
///
/// `DirEntry` represents an entry inside a directory on a filesystem that can be inspected to
/// learn about the entry.
pub trait DirEntry {
    /// Metadata is an associated type until traits can return `impl Trait`.
    type Metadata: Metadata;
    /// FileType is an associated type until traits can return `impl Trait`.
    type FileType: FileType;

    /// Returns the full path to the file or directory this entry represents.
    fn path(&self) -> PathBuf;
    /// Returns metadata for the file this entry represents.
    fn metadata(&self) -> Result<Self::Metadata>;
    /// Returns the file type for what this entry points at.
    fn file_type(&self) -> Result<Self::FileType>;
    /// Returns the base name of the file or directory this entry represents.
    fn file_name(&self) -> OsString;
}

/// A reference to an open file on the filesystem.
///
/// This is meant to mirror `std::fs::File`, but only provides a few important functions. Sync is
/// deliberately left out as, on most systems, it is a noop or worse yet, a lie. A proper sync, to
/// ensure data is 100% truly on disk, requires a complicated sequence that is different on most
/// systems.
pub trait File: Read + Seek + Write + Sized {
    /// Metadata is an associated type until traits can return `impl Trait`.
    type Metadata: Metadata;
    /// Permissions is an associated type until traits can return `impl Trait`.
    type Permissions: Permissions;

    fn sync_all(&self) -> Result<()>;
    fn sync_data(&self) -> Result<()>;
    fn set_len(&self, size: u64) -> Result<()>;
    /// Queries information about the underlying file.
    fn metadata(&self) -> Result<Self::Metadata>;
    fn try_clone(&self) -> Result<Self>;
    fn set_permissions(&self, perm: Self::Permissions) -> Result<()>;
}

/// Represents the type of a file.
pub trait FileType {
    /// Returns whether this file type is a directory.
    fn is_dir(&self) -> bool;
    /// Returns whether this file type is a file.
    fn is_file(&self) -> bool;
    /// TODO doc and examples
    fn is_symlink(&self) -> bool;
}

/// Metadata information about a file.
pub trait Metadata {
    /// Permissions is an associated type until traits can return `impl Trait`.
    type Permissions: Permissions;
    /// FileType is an associated type until traits can return `impl Trait`.
    type FileType: FileType;

    /// Returns the file type for this metadata.
    fn file_type(&self) -> Self::FileType;
    /// Returns whether this metadata is for a directory.
    fn is_dir(&self) -> bool;
    /// Returns whether this metadata is for a file.
    fn is_file(&self) -> bool;
    /// Returns the size, in bytes, of the file this metadata is for.
    fn len(&self) -> u64;
    /// Returns the permissions of the file this metadata is for.
    fn permissions(&self) -> Self::Permissions;
    /// Returns whether the file is empty. This defaults to checking `len() == 0`.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Options and flags which can be used to configure how a file is opened.
///
/// This trait replaces [`std::fs::OpenOptions`] with the exception of its `new` function. To create
/// a new `OpenOptions`, use [`GenFS::new_openopts`].
///
/// [`std::fs::OpenOptions`]: https://doc.rust-lang.org/std/fs/struct.OpenOptions.html
/// [`GenFS::new_openopts`]: trait.GenFS.html#tymethod.new_openopts
pub trait OpenOptions {
    /// File is an associated type until traits can return `impl Trait`.
    type File: File;

    /// Indicates the file's `read` state once opened.
    fn read(&mut self, read: bool) -> &mut Self;
    /// Indicates the file's `write` state once opened.
    fn write(&mut self, write: bool) -> &mut Self;
    /// Indicates whether writes should always append to the end of the file (even if other writes
    /// occured) or from the current write position. See `std::fs::OpenOptions` for more
    /// information.
    fn append(&mut self, append: bool) -> &mut Self;
    /// Indicates whether the file should be truncated on open.
    fn truncate(&mut self, truncate: bool) -> &mut Self;
    /// Sets the option to create the file if it does not exist. `write` or `append` must be used
    /// with this option.
    fn create(&mut self, create: bool) -> &mut Self;
    /// Sets the option to exclusively create this file. If the file already exists, `open` will
    /// fail. `write` or `append` must be used with this option.
    fn create_new(&mut self, create_new: bool) -> &mut Self;
    /// Opens the file at `path`.
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File>;
}

/// Representation of the various permissions on a file.
pub trait Permissions {
    /// Returns whether these permissions have readonly set.
    fn readonly(&self) -> bool;
    /// Modifies the readonly fly for these permissions.
    ///
    /// This does not modify the filesystem. To modify the filesystem, use the filesystem's
    /// [`set_permissions`] function.
    ///
    /// [`set_permissions`]: trait.GenFS.html#tymethod.set_permissions
    fn set_readonly(&mut self, readonly: bool);
}

/// The single filesystem underpinning all filesystem operations.
///
/// This trait intends to be a drop in replacement for most uses of [`std::fs`]. As with
/// [`std::fs`], all methods in this trait are cross platform. Extra platform specific
/// functionality can be found in the extension traits of `rsfs::$platform_ext`.
///
/// [`std::fs`]: https://doc.rust-lang.org/std/fs/
pub trait GenFS {
    /// DirBuilder is an associated type until traits can return `impl Trait`.
    type DirBuilder: DirBuilder;
    /// DirEntry is an associated type until traits can return `impl Trait`.
    type DirEntry: DirEntry;
    /// File is an associated type until traits can return `impl Trait`.
    type File: File;
    /// Metadata is an associated type until traits can return `impl Trait`.
    type Metadata: Metadata;
    /// OpenOptions is an associated type until traits can return `impl Trait`.
    type OpenOptions: OpenOptions;
    /// Permissions is an associated type until traits can return `impl Trait`.
    type Permissions: Permissions;
    /// ReadDir is an associated type until traits can return `impl Trait`.
    type ReadDir: Iterator<Item = Result<Self::DirEntry>>;

    fn copy<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<u64>;

    /// Creates a new, empty directory at the provided path.
    fn create_dir<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Recursively creates a directory and all its parent components if they are missing.
    fn create_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// TODO doc, as well as examples for everything, and errors
    fn hard_link<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()>;

    /// Returns metadata information of the file or directory at path.
    ///
    /// This function will traverse symbolic links to query a directory or file.
    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata>;

    /// Returns an iterator over entries within a directory.
    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<Self::ReadDir>;

    // TODO doc and examples
    fn read_link<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf>;

    /// Removes an existing, empty directory.
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Removes a directory at path after removing all of its contents.
    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Removes a file from the filesystem.
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()>;

    /// Renames a file or directory at `from` to `to`, replacing `to` if it exists (and, for a
    /// directory, is empty).
    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()>;

    /// Changes the permissions of a file or directory.
    fn set_permissions<P: AsRef<Path>>(&self, path: P, perm: Self::Permissions) -> Result<()>;

    /// TODO
    fn symlink_metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata>;

    /// Returns a new OpenOptions for a file for this filesytem.
    ///
    /// This method replaces [`std::fs::OpenOptions::new()`], which now needs to be a part of this
    /// trait to ensure any new file belongs to the `GenFS` that created the `OpenOptions`.
    ///
    /// [`std::fs::OpenOptions::new()`]: https://doc.rust-lang.org/std/fs/struct.OpenOptions.html#method.new
    fn new_openopts(&self) -> Self::OpenOptions;

    /// Returns a new DirBuilder for a directory for this filesystem.
    ///
    /// This method replaces [`std::fs::DirBuilder::new()`], which now needs to be a part of this
    /// trait to ensure any new directory belongs to the `GenFS` that created the `DirBuilder`.
    ///
    /// [`std::fs::DirBuilder::new()`]: https://doc.rust-lang.org/std/fs/struct.DirBuilder.html#method.new
    fn new_dirbuilder(&self) -> Self::DirBuilder;

    /// TODO doc, clean all docs.
    fn file_open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File>;
    fn file_create<P: AsRef<Path>>(&self, path: P) -> Result<Self::File>;
}
