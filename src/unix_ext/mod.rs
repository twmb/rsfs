//! This module provides Unix specific traits that extend the traits in [`rsfs`].
//!
//! This module is only available on Unix systems. The trait's functions are separate from `rsfs`
//! traits to ensure users of these traits know they are using Unix specific functionality.
//!
//! # Example
//!
//! ```
//! use rsfs::*;
//! use rsfs::unix_ext::*;
//!
//! use rsfs::disk::fs;
//!
//! let fs = fs::FS;
//! assert!(fs.metadata("/").unwrap().permissions().mode() == 0o755);
//! ```
//!
//! [`rsfs`]: ../index.html

use std::io::Result;
use std::path::Path;

/// A Unix specific [`rsfs::DirBuilder`] extension.
///
/// [`rsfs::DirBuilder`]: ../trait.DirBuilder.html
pub trait DirBuilderExt {
    /// Sets the mode bits to create new directories with. This option defaults to 0o777.
    fn mode(&mut self, mode: u32) -> &mut Self;
}

/// A Unix specific [`rsfs::OpenOptions`] extension.
///
/// [`rsfs::OpenOptions`]: ../trait.OpenOptions.html
pub trait OpenOptionsExt {
    /// Sets the mode bits that a new file will be opened with.
    ///
    /// The default mode for new files is 0o666.
    fn mode(&mut self, mode: u32) -> &mut Self;
    fn custom_flags(&mut self, flags: i32) -> &mut Self;
}

/// A Unix specific [`rsfs::Permissions`] extension.
///
/// [`rsfs::Permissions`]: ../trait.Permissions.html
pub trait PermissionsExt {
    /// Returns the underlying Unix mode of these permissions.
    fn mode(&self) -> u32;
    /// Sets the underlying Unix mode for these permissions.
    ///
    /// This does not modify the filesystem. To modify the filesystem, use the filesystem's
    /// [`set_permissions`] function.
    ///
    /// [`set_permissions`]: ../trait.FS.html#tymethod.set_permissions
    fn set_mode(&mut self, mode: u32);
    /// Creates a new Permissions from the given Unix mode.
    fn from_mode(mode: u32) -> Self;
}

pub trait FileExt {
    fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize>;
    fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize>;
}

pub trait FSExt {
    // TODO doc
    fn symlink<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()>;
}
