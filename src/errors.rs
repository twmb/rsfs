//! Common filesystem errors.
//!
//! This module provides convenience functions for generating [`io::Error`]s from OS error codes.
//! Notably, these errors are the only errors returned in the [`mem`] module if using implemented
//! behavior (unimplemented behavior returns `Error::new::ErrorKind::Other`).
//!
//! [`io::Error`]: https://doc.rust-lang.org/std/io/struct.Error.html
//! [`mem`]: ../mem/index.html

use std::io::Error;

/// Used when a file or directory does not exist.
#[allow(non_snake_case)]
pub fn ENOENT() -> Error {
    Error::from_raw_os_error(2)
}

/// Used when performing an operation with a file that was not opened in a way to allow that
/// operation (read on a write only open, etc).
#[allow(non_snake_case)]
pub fn EBADF() -> Error {
    Error::from_raw_os_error(9)
}

/// Used when a user does not have requisite permissions.
#[allow(non_snake_case)]
pub fn EACCES() -> Error {
    Error::from_raw_os_error(13)
}

/// Used when a file or directory does not exist.
#[allow(non_snake_case)]
pub fn EEXIST() -> Error {
    Error::from_raw_os_error(17)
}

/// Used when attempting to perform a directory operation on a file.
#[allow(non_snake_case)]
pub fn ENOTDIR() -> Error {
    Error::from_raw_os_error(20)
}

/// Used when attempting to perform a file operation on a directory.
#[allow(non_snake_case)]
pub fn EISDIR() -> Error {
    Error::from_raw_os_error(21)
}

/// Used when performing an invalid operation (aka, a bad OpenOptions combination).
#[allow(non_snake_case)]
pub fn EINVAL() -> Error {
    Error::from_raw_os_error(22)
}

/// Used when an operation needs an empty directory and is performed on a non-empty directory.
#[allow(non_snake_case)]
pub fn ENOTEMPTY() -> Error {
    // TODO Windows is 41, other Unix / BSD distros differ from 39.
    Error::from_raw_os_error(39)
}
