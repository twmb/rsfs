//! An in memory filesystem that allows error injection.
//!
//! The [`FS`] provides an in memory file system that allows injecting errors. This module is built
//! on top of the [`mem`] module provided by this crate; read that module documentation first to
//! understand how the in memory aspects of this filesystem will behave.
//!
//! Injected errors are consumed via a FIFO queue. The calling API passes a sequence of closures
//! that will be passed which function a filesystem call is in if the function can error. The
//! sequence of closures is drained as they return `Some(Result)`; if a closure returns `None`, the
//! closure is not drained from the sequence.
//!
//! While I believe the API is already useful, I can imagine many ways this could be improved to
//! add more exact error injection to cause more precise cascading failures. These additions will
//! likely be API changing. Versions under 1 may see some of this change, but after 1.0, I will
//! increment the major version as the API changes.
//!
//! # Example
//!
//! ```
//! use rsfs::*;
//! use rsfs::errors::*;
//! use rsfs::mem::test::fs::{FS, InKind, AtFile};
//! use std::io::{Read, Result, Seek, SeekFrom, Write};
//!
//! let fs = FS::with_mode(0o300);
//!
//! // push a sequence that we want to trigger failure on:
//! // a successful read followed by a failure.
//!
//! fs.push_sequence(vec![Box::new(|k: InKind| -> Option<Result<()>> { // successful first
//!                           if k == InKind::File(AtFile::Read) {
//!                               return Some(Ok(()));
//!                           }
//!                           None
//!                       }),
//!                       Box::new(|k: InKind| -> Option<Result<()>> { // failing second
//!                           if k == InKind::File(AtFile::Read) {
//!                               return Some(Err(ENOENT()));
//!                           }
//!                           None
//!                       })]);
//!
//! // open a file, write some content...
//! let mut wf =
//!     fs.new_openopts().mode(0o600).write(true).create_new(true).open("f").unwrap();
//! assert_eq!(wf.write(vec![0, 1, 2, 3, 4, 5].as_slice()).unwrap(), 6);
//!
//! // open the file for reading...
//! let mut rf = fs.new_openopts().read(true).open("f").unwrap();
//!
//! // read some content, consuming the first closure in the sequence...
//! let mut output = [0u8; 4];
//! assert_eq!(rf.read(&mut output).unwrap(), 4);
//! assert_eq!(&output, &[0, 1, 2, 3]);
//!
//! // notice that other file operations will not fail
//! assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);
//!
//! // consume the second closure, which will error...
//! assert!(rf.read(&mut output).is_err());
//!
//! // now we are back to normal and that same read will be successful...
//! assert_eq!(rf.read(&mut output).unwrap(), 4);
//! assert_eq!(&output, &[1, 2, 3, 4]);
//! ```
//!
//! [`FS`]: struct.FS.html
//! [`mem`]: ../mem/index.html

// TODO: I think it would be good for the enums to also take references to the arguments of the
// function the enums are used in, which would allow for exact matching for APIs to use when
// determining whether an error should occur.
// Additionally, it would be super useful to trigger partial reads or writes.

extern crate parking_lot;

use self::parking_lot::Mutex;

use fs;
use mem::fs as mem;

use std::collections::VecDeque;
use std::ffi::OsString;
use std::io::{Read, Result, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// The `testfs` is about to call a [`File`] method.
///
/// [`File`]: ../fs/trait.File.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AtFile {
    /// The next call will be [`read`].
    ///
    /// [`read`]: https://doc.rust-lang.org/nightly/std/io/trait.Read.html#tymethod.read
    Read,
    /// The next call will be [`write`].
    ///
    /// [`write`]: https://doc.rust-lang.org/nightly/std/io/trait.Write.html#tymethod.write
    Write,
    /// The next call will be [`flush`].
    ///
    /// [`flush`]: https://doc.rust-lang.org/nightly/std/io/trait.Write.html#tymethod.flush
    Flush,
    /// The next call will be [`seek`].
    ///
    /// [`seek`]: https://doc.rust-lang.org/std/io/trait.Seek.html#tymethod.seek
    Seek,
    /// The next call will be [`metadata`].
    ///
    /// [`metadata`]: ../fs/trait.File.html#tymethod.metadata
    Metadata,
}

/// The `testfs` is about to call an [`OpenOptions`] method.
///
/// [`OpenOptions`]: ../fs/trait.OpenOptions.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AtOpenOpts {
    /// The next call will be [`open`].
    ///
    /// [`open`]: ../fs/trait.OpenOptions.html#tymethod.open
    Open,
}

/// The `testfs` is about to call a [`DirBuilder`] method.
///
/// [`DirBuilder`]: ../fs/trait.DirBuilder.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AtDirBuilder {
    /// The next call will be [`create`].
    ///
    /// [`create`]: ../fs/trait.DirBuilder.html#tymethod.create
    Create,
}

/// The `testfs` is about to call a [`DirEntry`] method.
///
/// [`DirEntry`]: ../fs/trait.DirEntry.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AtDirEntry {
    /// The next call will be [`metadata`].
    ///
    /// [`metadata`]: ../fs/trait.DirEntry.html#tymethod.metadata
    Metadata,
}

/// The `testfs` is about to call a [`ReadDir`] method.
///
/// [`ReadDir`]: ../fs/trait.ReadDir.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AtReadDir {
    /// The next call will be [`next`].
    ///
    /// [`next`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#tymethod.next
    Next,
}

/// The `testfs` is about to call an [`FS`] method.
///
/// [`FS`]: ../fs/trait.FS.html
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AtFS {
    /// The next call will be [`metadata`].
    ///
    /// [`metadata`]: ../fs/trait.FS.html#tymethod.metadata
    Metadata,
    /// The next call will be [`read_dir`].
    ///
    /// [`read_dir`]: ../fs/trait.FS.html#tymethod.read_dir
    ReadDir,
    /// The next call will be [`rename`].
    ///
    /// [`rename`]: ../fs/trait.FS.html#tymethod.rename
    Rename,
    /// The next call will be [`remove_dir`].
    ///
    /// [`remove_dir`]: ../fs/trait.FS.html#tymethod.remove_dir
    RemoveDir,
    /// The next call will be [`remove_dir_all`].
    ///
    /// [`remove_dir_all`]: ../fs/trait.FS.html#tymethod.remove_dir_all
    RemoveDirAll,
    /// The next call will be [`remove_file`].
    ///
    /// [`remove_file`]: ../fs/trait.FS.html#tymethod.remove_file
    RemoveFile,
}

/// The `testfs` is about to call a method that can error.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum InKind {
    /// The `testfs` is about to call a [`File`] method. See the [`AtFile`] enum.
    ///
    /// [`File`]: ../fs/trait.File.html
    /// [`AtFile`]: enum.AtFile.html
    File(AtFile),
    /// The `testfs` is about to call an [`OpenOptions`] method. See the
    /// [`AtOpenOptions`] enum.
    ///
    /// [`OpenOptions`]: ../fs/trait.OpenOptions.html
    /// [`AtOpenOptions`]: enum.AtOpenOptions.html
    OpenOptions(AtOpenOpts),
    /// The `testfs` is about to call a [`DirBuilder`] method. See the [`AtDirBuilder`]
    /// enum.
    ///
    /// [`DirBuilder`]: ../fs/trait.DirBuilder.html
    /// [`AtDirBuilder`]: enum.AtDirBuilder.html
    DirBuilder(AtDirBuilder),
    /// The `testfs` is about to call a [`DirEntry`] method. See the [`AtDirEntry`] enum.
    ///
    /// [`DirEntry`]: ../fs/trait.DirEntry.html
    /// [`AtDirEntry`]: enum.AtDirEntry.html
    DirEntry(AtDirEntry),
    /// The `testfs` is about to call a [`ReadDir`] method. See the [`AtReadDir`] enum.
    ///
    /// [`ReadDir`]: ../fs/trait.ReadDir.html
    /// [`AtReadDir`]: enum.AtReadDir.html
    ReadDir(AtReadDir),
    /// The `testfs` is about to call an [`FS`] method. See the [`AtFS`] enum.
    ///
    /// [`FS`]: ../fs/trait.FS.html
    /// [`AtFS`]: enum.AtFS.html
    FS(AtFS),
}

/// A view into a file on the filesystem.
///
/// This struct wraps [`mem::File`] with the addition that file methods can potentially consume
/// [`testfs`] injected errors. See the module [documentation] for an example.
///
/// [`mem::File`]: ../mem/struct.File.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct File {
    seq: ResultSeq,
    inner: mem::File,
}

impl fs::File for File {
    type Metadata = mem::Metadata;

    fn metadata(&self) -> Result<Self::Metadata> {
        self.seq.maybe_seq(InKind::File(AtFile::Metadata))?;
        self.inner.metadata()
    }
}

impl Read for File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.seq.maybe_seq(InKind::File(AtFile::Read))?;
        self.inner.read(buf)
    }
}

impl Write for File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.seq.maybe_seq(InKind::File(AtFile::Write))?;
        self.inner.write(buf)
    }
    fn flush(&mut self) -> Result<()> {
        self.seq.maybe_seq(InKind::File(AtFile::Flush))?;
        self.inner.flush()
    }
}

impl Seek for File {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        self.seq.maybe_seq(InKind::File(AtFile::Seek))?;
        self.inner.seek(pos)
    }
}

/// Options and flags which can be used to configure how a file is opened.
///
/// This struct wraps [`mem::OpenOptions`] with the addition that `.open()` can potentially consume
/// a [`testfs`] injected error. See the module [documentation] for an example.
///
/// [`mem::OpenOptions`]: ../mem/struct.OpenOptions.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct OpenOptions {
    seq: ResultSeq,
    inner: mem::OpenOptions,
}

impl fs::OpenOptions for OpenOptions {
    type File = File;

    fn read(&mut self, read: bool) -> &mut Self {
        self.inner.read(read);
        self
    }
    fn write(&mut self, write: bool) -> &mut Self {
        self.inner.write(write);
        self
    }
    fn append(&mut self, append: bool) -> &mut Self {
        self.inner.append(append);
        self
    }
    fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.inner.truncate(truncate);
        self
    }
    fn create(&mut self, create: bool) -> &mut Self {
        self.inner.create(create);
        self
    }
    fn create_new(&mut self, create_new: bool) -> &mut Self {
        self.inner.create_new(create_new);
        self
    }
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.inner.mode(mode);
        self
    }
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        self.seq.maybe_seq(InKind::OpenOptions(AtOpenOpts::Open))?;
        self.inner.open(path).map(|f| {
            File {
                seq: self.seq.clone(),
                inner: f,
            }
        })
    }
}

/// A builder used to create directories in various manners.
///
/// This struct wraps [`mem::DirBuilder`] with the addition that `.create()` can potentially
/// consume a [`testfs`] injected error. See the module [documentation] for an example.
///
/// [`mem::DirBuilder`]: ../mem/struct.DirBuilder.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct DirBuilder {
    seq: ResultSeq,
    inner: mem::DirBuilder,
}

impl fs::DirBuilder for DirBuilder {
    fn recursive(&mut self, recursive: bool) -> &mut Self {
        self.inner.recursive(recursive);
        self
    }
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.inner.mode(mode);
        self
    }
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.seq.maybe_seq(InKind::DirBuilder(AtDirBuilder::Create))?;
        self.inner.create(path)
    }
}

/// Entries returned by the [`ReadDir`] iterator.
///
/// This struct wraps [`mem::DirEntry`] with the addition that `.metadata()` can potentially
/// consume a [`testfs`] injected error. See the module [documentation] for an example.
///
/// [`ReadDir`]: struct.ReadDir.html
/// [`mem::DirEntry`]: ../mem/struct.DirEntry.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct DirEntry {
    seq: ResultSeq,
    inner: mem::DirEntry,
}

impl fs::DirEntry for DirEntry {
    type Metadata = mem::Metadata;

    fn path(&self) -> PathBuf {
        self.inner.path()
    }
    fn file_name(&self) -> OsString {
        self.inner.file_name()
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        self.seq.maybe_seq(InKind::DirEntry(AtDirEntry::Metadata))?;
        self.inner.metadata()
    }
}

/// Iterator over entries in a directory.
///
/// This struct wraps [`mem::ReadDir`] with the addition that `.next()` can potentially consume
/// [`testfs`] injected errors. See the module [documentation] for an example.
///
/// [`mem::ReadDir`]: ../mem/struct.ReadDir.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct ReadDir {
    seq: ResultSeq,
    inner: mem::ReadDir,
}

impl Iterator for ReadDir {
    type Item = Result<DirEntry>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Err(e) = self.seq.maybe_seq(InKind::ReadDir(AtReadDir::Next)) {
            return Some(Err(e));
        }
        self.inner.next().map(|res| {
            res.map(|dirent| {
                DirEntry {
                    seq: self.seq.clone(),
                    inner: dirent,
                }
            })
        })
    }
}

#[derive(Clone)]
struct ResultSeq(Arc<Mutex<VecDeque<Box<Fn(InKind) -> Option<Result<()>>>>>>); // >>>>>>>>>>>

impl ResultSeq {
    // maybe_seq calls the front sequence closure if it exists and, if that closure returned
    // something, pops the front and returns that something.
    fn maybe_seq(&self, in_kind: InKind) -> Result<()> {
        let mut seq = self.0.lock();
        match seq.front().map_or(None, |seq| seq(in_kind)) {
            Some(res) => {
                seq.pop_front();
                res
            }
            None => Ok(()),
        }
    }
}

/// An in memory struct that satisfies [`rsfs::FS`] and allows for injectable errors.
///
/// `FS` is thread safe and copyable. It wraps [`mem::FS`] with an ability to inject errors. This
/// should be generally useful for triggering error conditions in your code that generally are
/// untestable otherwise.
///
/// See the module [documentation] for an example.
///
/// [`rsfs::FS`]: ../trait.FS.html
/// [`mem::FS`]: ../mem/struct.FS.html
/// [documentation]: index.html
#[derive(Clone)]
pub struct FS {
    seq: ResultSeq,
    inner: mem::FS,
}

impl FS {
    /// Creates an empty `FS` with mode `0o775`.
    pub fn new() -> FS {
        Self::with_mode(0o775)
    }

    /// Creates an empty `FS` with the given mode.
    pub fn with_mode(mode: u32) -> FS {
        FS {
            seq: ResultSeq(Arc::new(Mutex::new(VecDeque::new()))),
            inner: mem::FS::with_mode(mode),
        }
    }

    /// Changes the current working directory of the filesytsem.
    ///
    /// This call simply calls [`cd`] on the wrapped [`mem::FS`].
    ///
    /// NOTE: This does not consume from sequence errors as this should only be used while setting
    /// up a test filesystem.
    ///
    /// [`cd`]: ../mem/struct.FS.html#method.cd
    /// [`mem::FS`]: ../mem/struct.FS.html
    pub fn cd<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.inner.cd(path)
    }

    /// Changes the file or directory at `path`'s mode.
    ///
    /// This call simply calls [`chmod`] on the wrapped [`mem::FS`].
    ///
    /// NOTE: This does not consume from sequence errors as this should only be used while setting
    /// up a test filesystem.
    ///
    /// [`chmod`]: ../mem/struct.FS.html#method.chmod
    /// [`mem::FS`]: ../mem/struct.FS.html
    pub fn chmod<P: AsRef<Path>>(&self, path: P, mode: u32) -> Result<()> {
        self.inner.chmod(path, mode)
    }

    /// Pushes a sequence of closures to run on future operations that return `Result`.
    ///
    /// On every filesystem call that returns `Result`, a `testfs` checks the head of an internal
    /// sequence of closures. If one exists, it calls that closure with an enum signalling what
    /// call it is about to perform. With this information, the closure can return whether that
    /// operation should fail and if so, with what error.
    ///
    /// Closures in the sequence are only consumed once they return `Some` value. By returning a
    /// series of `Some` values, this sequence can trigger cascading errors during testing that
    /// normally are untestable.
    ///
    /// See the module [documentation] for an example.
    ///
    /// [documentation]: index.html
    pub fn push_sequence(&self, seq: Vec<Box<Fn(InKind) -> Option<Result<()>>>>) {
        let mut existing = self.seq.0.lock();
        for c in seq {
            existing.push_back(c);
        }
    }

    /// Clears the internal sequence of errors, if any.
    ///
    /// Future operations will proceed as normal unless more errors are injected.
    pub fn clear_sequence(&self) {
        self.seq.0.lock().clear()
    }
}

impl fs::GenFS for FS {
    type Metadata = mem::Metadata;
    type OpenOptions = OpenOptions;
    type DirBuilder = DirBuilder;
    type DirEntry = DirEntry;
    type ReadDir = ReadDir;

    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<mem::Metadata> {
        self.seq.maybe_seq(InKind::FS(AtFS::Metadata))?;
        self.inner.metadata(path)
    }
    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<ReadDir> {
        self.seq.maybe_seq(InKind::FS(AtFS::ReadDir))?;
        let res = self.inner.read_dir(path)?;
        Ok(ReadDir {
            seq: self.seq.clone(),
            inner: res,
        })
    }
    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        self.seq.maybe_seq(InKind::FS(AtFS::Rename))?;
        self.inner.rename(from, to)
    }
    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.seq.maybe_seq(InKind::FS(AtFS::RemoveDir))?;
        self.inner.remove_dir(path)
    }
    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.seq.maybe_seq(InKind::FS(AtFS::RemoveDirAll))?;
        self.inner.remove_dir_all(path)
    }
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.seq.maybe_seq(InKind::FS(AtFS::RemoveFile))?;
        self.inner.remove_file(path)
    }
    fn new_openopts(&self) -> OpenOptions {
        OpenOptions {
            seq: self.seq.clone(),
            inner: self.inner.new_openopts(),
        }
    }
    fn new_dirbuilder(&self) -> DirBuilder {
        DirBuilder {
            seq: self.seq.clone(),
            inner: self.inner.new_dirbuilder(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use errors::*;
    use fs::{DirBuilder, GenFS, OpenOptions};
    use std::io::{Error, Read, Seek, SeekFrom, Write};

    fn errs_eq(l: Error, r: Error) -> bool {
        l.raw_os_error() == r.raw_os_error()
    }

    #[test]
    fn basic() {
        let fs = FS::with_mode(0o300);
        assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());

        // Push a few errors (rustfmt makes this hideous)...
        fs.push_sequence(vec![// Fail creating a directory...
                              Box::new(|k: InKind| -> Option<Result<()>> {
            match k {
                InKind::DirBuilder(AtDirBuilder::Create) => Some(Err(ENOENT())),
                _ => None,
            }
        }),
                              // After which, one read must succeed.
                              Box::new(|k: InKind| -> Option<Result<()>> {
                                  match k {
                                      InKind::File(AtFile::Read) => Some(Ok(())),
                                      _ => None,
                                  }
                              }),
                              // Then fail the next read.
                              Box::new(|k: InKind| -> Option<Result<()>> {
                                  match k {
                                      InKind::File(AtFile::Read) => Some(Err(EACCES())),
                                      _ => None,
                                  }
                              })]);

        // open a file, write some content...
        let mut wf =
            fs.new_openopts().mode(0o600).write(true).create_new(true).open("a/f").unwrap();
        assert_eq!(wf.write(vec![0, 1, 2, 3, 4, 5].as_slice()).unwrap(), 6);

        // open the file for reading, read some content...
        let mut rf = fs.new_openopts().read(true).open("a/f").unwrap();
        assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);

        let mut output = [0u8; 4];
        assert_eq!(rf.read(&mut output).unwrap(), 4);
        assert_eq!(&output, &[1, 2, 3, 4]);

        // intermix consuming the errors with non-failures.
        assert!(errs_eq(fs.new_dirbuilder().create("a/d").unwrap_err(), ENOENT())); // error 1
        assert!(fs.new_dirbuilder().create("a/d").is_ok());
        assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);
        assert_eq!(rf.read(&mut output).unwrap(), 4); // ok 2
        assert_eq!(&output, &[1, 2, 3, 4]);
        assert_eq!(rf.seek(SeekFrom::Start(2)).unwrap(), 2);
        assert!(errs_eq(rf.read(&mut output).unwrap_err(), EACCES())); // error 3
        // and now we are back to normal
        assert_eq!(rf.read(&mut output).unwrap(), 4);
        assert_eq!(&output, &[2, 3, 4, 5]);
    }
}
