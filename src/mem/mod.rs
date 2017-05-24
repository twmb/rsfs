//! An in memory filesystem.
//!
//! The [`FS`] provides an in memory file system. Only a Unix implementation is currently
//! available. Errors returned attempt to mimic true operating sytsem  error codes, but may not
//! catch subtle differences between operating systems.
//!
//! This crate should provide a decent alternative to FUSE if there is no need to use your in
//! memory filesystem outside of your process.
//!
//! # Example
//!
//! ```
//! use std::io::{Read, Seek, SeekFrom, Write};
//! use std::path::PathBuf;
//!
//! use rsfs::*;
//! use rsfs::mem::FS;
//!
//! // setup our filesystem
//!
//! let fs = FS::new();
//! assert!(fs.create_dir_all("a/b/c").is_ok());
//!
//! // open a file, write to it, and read from it
//!
//! let mut wf = fs.create_file("a/f").unwrap();
//! assert_eq!(wf.write(vec![0, 1, 2, 3, 4, 5].as_slice()).unwrap(), 6);
//!
//! let mut rf = fs.open_file("a/f").unwrap();
//! assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);
//!
//! let mut output = [0u8; 4];
//! assert_eq!(rf.read(&mut output).unwrap(), 4);
//! assert_eq!(&output, &[1, 2, 3, 4]);
//! ```
//!
//! [`FS`]: struct.FS.html
//! [`unix_ext`]: ../unix_ext/index.html
//! [`errors`]: ../errors/index.html

#[cfg(unix)]
#[path = "unix.rs"]
mod fs;

pub use self::fs::*;

pub mod test;
