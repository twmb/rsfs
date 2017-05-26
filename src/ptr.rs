extern crate core;

use self::core::nonzero::NonZero;
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ops::{Deref, DerefMut};

/// `Raw` is like `Unique`, but even more unsafe. This is specifically meant to be an unsafe
/// wrapper around `*mut T` and should be used extremely carefully. The primary purpose is to make
/// it very easy to work with `*mut T` by implementing `Deref` and `DerefMut` with their targets
/// being &T and `&mut T`.
pub struct Raw<T: ?Sized> {
    ptr: NonZero<*const T>,
    mkr: PhantomData<T>,
}

impl<T: ?Sized> Raw<T> {
    pub const fn new(ptr: *mut T) -> Raw<T> {
        unsafe { Raw { ptr: NonZero::new(ptr), mkr: PhantomData } }
    }

    pub fn ptr(&self) -> *mut T {
        unsafe { mem::transmute(self.ptr.get()) }
    }

    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.ptr.get() == other.ptr.get()
    }
}

impl<T: ?Sized> Clone for Raw<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for Raw<T> { }

unsafe impl<T: Send + ?Sized> Send for Raw<T> { }
unsafe impl<T: Sync + ?Sized> Sync for Raw<T> { }

impl<T: ?Sized> Deref for Raw<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.ptr.get() }
    }
}

impl<T: ?Sized> DerefMut for Raw<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr() }
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Raw<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }    
}

impl<T> From<T> for Raw<T> {
	fn from(t: T) -> Raw<T> {
        Raw::new(Box::into_raw(Box::new(t)))
    }
}
