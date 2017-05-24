//! A generic filesystem with implementations for normal (disk), in memory, and test work sets.
//!
//! # Reason for existence
//!
//! The [`std::fs`] module provides functions to manipulate the filesytem, and these functions are
//! good. However, if you have code that uses `std::fs`, it is difficult to ensure that your code
//! handles errors properly because generally, you are not testing on an already broken machine.
//! You could attempt to set up FUSE, which, although doable, is involved.
//!
//! This crate provides a generic filesystem with various implementations, one of which is an
//! in-memory filesystem that can have defined error injection. The intent of this crate is for you
//! to use the generic [`rsfs::FS`] everywhere where you use `std::fs` in your code. Your `main.rs`
//! can use [`rsfs::disk::FS`] to get default disk behavior while your tests use
//! [`rsfs::mem::test::FS`] to get an in-memory filesystem that can have errors injected.
//!
//! # An in-memory filesystem
//!
//! The injectable in-memory filesystem is a small shim that wraps a solid in-memory filesystem.
//! There existed no complete in-process in-memory filesystem when I wrote this crate. I believe
//! the implementation in [`rsfs::mem`] should suffice for most future needs.
//!
//! # Caveats
//!
//! The current in-memory filesystems are only implemented for Unix. Window's users can help by
//! implementing the in-memory analog for Windows.
//!
//! The in-memory filesystem is implemented using some unsafe code. I deemed this necessary after
//! working with the recursive data structure that is a filesystem through an Arc/RwLock for too
//! long. The code is pretty well tested; there should be no problems. The usage of unsafe, in my
//! opinion, makes the code much clearer, but it did require special care in some functions.
//!
//! Lastly, this crate makes use of nightly's (as of Rust 1.18) [`NonZero`] struct. Hopefully this
//! will be stablized soon, but usage of this crate currently forces nightly.
//!
//! # Documentation credit
//!
//! This crate copies _a lot_ of the documentation and examples that currently exist in `std::fs`.
//! It not only makes it easier for people to migrate straight to this crate, but makes this crate
//! much more understandable. This crate includes Rust's MIT license in its repo for further
//! attribution purposes.
//!
//! [`std::fs`]: https://doc.rust-lang.org/std/fs/
//! [`rsfs::disk::FS`]: disk/struct.FS.html
//! [`rsfs::mem::test::FS`]: mem/test/struct.FS.html
//! [`rsfs::mem`]: mem/index.html
//! [`rsfs::FS`]: trait.FS.html
//! [`rsfs::rs`]: rs/index.html
//! [`rsfs::testfs`]: testfs/index.html
//! [`NonZero`]: https://doc.rust-lang.org/core/nonzero/struct.NonZero.html

#![feature(const_fn)]
#![feature(nonzero)]

mod fs;
pub use fs::*;

#[cfg(unix)]
pub mod unix_ext;

pub mod disk;
pub mod mem;

mod errors;
mod path_parts;
mod ptr;
