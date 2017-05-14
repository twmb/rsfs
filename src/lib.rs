//! A generic filesystem with implementations for normal (disk), in memory, and test work sets.
//!
//! The [`std::fs`] module provides functions to manipulate the filesytem and these functions are
//! fine. However, if you have code that uses [`std::fs`], it is difficult to ensure that your code
//! handles errors properly because generally, you are not testing on an already broken machine.
//! You could attempt to set up FUSE, which, although doable, is quite involved.
//!
//! This crate provides a generic filesystem with various implementations, one of which is an
//! in-memory filesystem that can have defined error injection. The intent of this crate is for you
//! to use the generic [`rsfs::FS`] everywhere where you use [`std::fs`] in your code. Your main
//! can use [`rsfs::rs`] to get default [`std::fs`] behavior while your tests can use
//! [`rsfs::testfs`] to get an in-memory filesystem where you are able to define how errors
//! propagate.
//!
//! Not all filesystem operations are implemented yet. If something is missing, please feel free to
//! implement it and open a PR to add it. Additionally, the current filesystem implementations are
//! all based around Unix systems. Window's users can help by opening PRs to add in Windows
//! specific behavior.
//!
//! The documentation of the traits in this module should closely resemble or be verbatim copies of
//! the [`std::fs`] documentation for the respective structs.
//!
//! [`std::fs`]: https://doc.rust-lang.org/std/fs/
//! [`rsfs::FS`]: trait.FS.html
//! [`rsfs::rs`]: rs/index.html
//! [`rsfs::testfs`]: testfs/index.html

#![feature(const_fn)]
#![feature(nonzero)]

mod fs;
pub use fs::*;

#[cfg(unix)]
pub mod unix_ext;

pub mod disk;
pub mod mem;
pub mod errors;
pub mod path_parts;

mod ptr;
