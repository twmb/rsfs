//! This module provides basic generic types for a filesystem.

use std::ffi::OsString;
use std::io::{Read, Seek, Write};
use std::io::Result;
use std::path::{Path, PathBuf};

pub trait Permissions {
    fn readonly(&self) -> bool;
    fn set_readonly(&mut self, readonly: bool);
}

pub trait FileType {
    fn is_dir(&self) -> bool;
    fn is_file(&self) -> bool;
}

/// Metadata information about a file.
///
/// This is meant to mirror `std::fs::Metadata`. A few less important functions are missing.
pub trait Metadata {
    /// Returns whether this metadata is for a directory.
    fn is_dir(&self) -> bool;
    /// Returns whether this metadata is for a file.
    fn is_file(&self) -> bool;
    /// Returns the size, in bytes, of the file this metadata is for.
    fn len(&self) -> u64;
    /// Returns the permissions of the file this metadata is for. This differs from `std::fs`'s
    /// Metadata's len in that this returns the mode, which is Unix specific, of the file.
    fn permissions(&self) -> u32;
    /// Returns whether the file is empty. This defaults to checking `len() == 0`.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// A reference to an open file on the filesystem.
///
/// This is meant to mirror `std::fs::File`, but only provides a few important functions. Sync is
/// deliberately left out as, on most systems, it is a noop and worse yet, a lie. A proper sync, to
/// ensure data is 100% truly on disk, requires a complicated sequence that is different on most
/// systems.
pub trait File: Read + Seek + Write {
    /// Metadata is an associated type until traits can return `impl Trait`.
    type Metadata: Metadata;

    /// Queries information about the underlying file.
    fn metadata(&self) -> Result<Self::Metadata>;
}

/// Options and flags which can be used to configure how a file is opened.
///
/// This mirrors `std::fs::OpenOptions`, but unconditionally requires `mode` (which, by default, is
/// hidden under unix's `OpenOptionsExt`, and this also requires an associated `File` type.
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
    /// Sets the mode bits that the file will be opened with. This is generally only useful when
    /// creating a new file.
    fn mode(&mut self, mode: u32) -> &mut Self;
    /// Opens the file at `path`.
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File>;
}

/// A builder used to create directories.
///
/// This mirrors `std::fs::DirBuilder`, but unconditionally requires `mode` (which, by default, is
/// hidden under unix's `DirBuilderExt`.
pub trait DirBuilder {
    /// Indicates that directories should be opened recursively, creating directories if they do
    /// not exist.
    fn recursive(&mut self, recursive: bool) -> &mut Self;
    /// Sets the mode bits to create new directories with (the default is 0o700).
    fn mode(&mut self, mode: u32) -> &mut Self; // Linux
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
    // TODO type FileType: FileType;

    /// Returns the full path to the file or directory this entry represents.
    fn path(&self) -> PathBuf;
    /// Returns metadata for the file this entry represents.
    fn metadata(&self) -> Result<Self::Metadata>;
    /// Returns the base name of the file or directory this entry represents.
    fn file_name(&self) -> OsString;

    // TODO fn file_type(&self) -> Result<FileType>
}

/// The filesystem underpinning all operations. All filesystem operations in code should use the
/// same, single filesystem that is created at initialization.
pub trait GenFS {
    /// Metadata is an associated type until traits can return `impl Trait`.
    type Metadata: Metadata;
    /// OpenOptions is an associated type until traits can return `impl Trait`.
    type OpenOptions: OpenOptions;
    /// DirBuilder is an associated type until traits can return `impl Trait`.
    type DirBuilder: DirBuilder;
    /// DirEntry is an associated type until traits can return `impl Trait`.
    type DirEntry: DirEntry;
    /// ReadDir is an associated type until traits can return `impl Trait`.
    type ReadDir: Iterator<Item = Result<Self::DirEntry>>;

    /// Returns the metadata of the file or directory at path.
    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Self::Metadata>;
    /// Returns an iterator of the entries within a directory.
    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<Self::ReadDir>;
    /// Removes an existing, empty directory.
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()>;
    /// Removes a directory at path after removing all of its contents.
    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()>;
    /// Removes a file from the filesystem.
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()>;
    /// Renames a file or directory at `from` to `to`, replacing `to` if it exists (and, for a
    /// directory, is empty).
    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()>;

    // TODO fn set_permissions<P: AsRef<Path>>(path: P, perm: Permissions) -> Result<()> is chmod

    /// Returns an OpenOptions for a file for this filesytem.
    fn new_openopts(&self) -> Self::OpenOptions;
    /// Returns a DirBuilder for a directory for this filesystem.
    fn new_dirbuilder(&self) -> Self::DirBuilder;
}
