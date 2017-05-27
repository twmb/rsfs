//! A generic filesystem with disk and in-memory implementations.
//!
//! # Reason for existence
//!
//! The [`std::fs`] module provides functions to manipulate the filesytem, and these functions are
//! good. However, if you have code that uses `std::fs`, it is difficult to ensure that your code
//! handles errors properly because generally, you are not testing on an already broken machine.
//! You could attempt to set up FUSE, which, although doable, is involved.
//!
//! This crate provides a generic filesystem with various implementations. At the moment, only
//! normal (non-injectable) disk and in-memory implementations are provided. In the future, an
//! error-injectable shim around the in-memory file system will be provided to help trigger
//! filesystem errors in unit tests.
//!
//! The intent of this crate is for you to use the generic [`rsfs::GenFS`] everywhere where you use
//! `std::fs` in your code. Your `main.rs` can use [`rsfs::disk::FS`] to get default disk behavior
//! while your tests use `rsfs::mem::test::FS` (once it exists) to get an in-memory filesystem that
//! can have errors injected.
//!
//! # An in-memory filesystem
//!
//! There existed no complete in-process in-memory filesystem when I wrote this crate; the
//! implementation in [`rsfs::mem`] should suffice most needs.
//!
//! `rsfs::mem` is a platform specific module that `pub use`s the proper module based off the
//! builder's platform. To get a platform agnostic module, you need to use the in-memory platform
//! you desire. Thus, if you use [`rsfs::mem::unix`], you will get an in-memory system that follows
//! Unix semantics. If you use `rsfs::mem::windows`, you will get an in-memory system that follows
//! Windows semantics (however, you would have to write that module first).
//!
//! This means that `rsfs::mem` aims to essentially be an in-memory drop in for `std::fs` and
//! forces you to structure your code in a cross-platform way. `rsfs::mem::unix` aims to be a Unix
//! specific drop in that buys you Unix semantics on all platforms.
//!
//! # Caveats
//!
//! The current in-memory filesystems are only implemented for Unix. This means that the only
//! cross-platform in-memory filesystem is specifically `rsfs::mem::unix`. Window's users can help
//! by implementing the in-memory analog for Windows.
//!
//! The in-memory filesystem is implemented using some unsafe code. I deemed this necessary after
//! working with the recursive data structure that is a filesystem through an `Arc`/`RwLock` for
//! too long. The code is pretty well tested; there should be no problems. The usage of unsafe, in
//! my opinion, makes the code much clearer, but it did require special care in some functions.
//!
//! # Documentation credit
//!
//! This crate copies _a lot_ of the documentation and examples that currently exist in `std::fs`.
//! It not only makes it easier for people to migrate straight to this crate, but makes this crate
//! much more understandable. This crate includes Rust's MIT license in its repo for further
//! attribution purposes.
//!
//! [`std::fs`]: https://doc.rust-lang.org/std/fs/
//! [`rsfs::GenFS`]: trait.GenFS.html
//! [`rsfs::disk::FS`]: disk/struct.FS.html
//! [`rsfs::mem`]: mem/index.html
//! [`rsfs::mem::unix`]: mem/unix/index.html

mod fs;
pub use fs::*;

pub mod disk;
pub mod mem;
pub mod unix_ext;

mod errors;
mod path_parts;
mod ptr;
