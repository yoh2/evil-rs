extern crate libc;
extern crate num;

use std::cmp::{Eq, PartialEq, Ord, PartialOrd, Ordering};

use std::ops::{Add, AddAssign};
use std::ops::{Sub, SubAssign};
use std::ops::{Deref, DerefMut};
use std::ops::{Index, IndexMut};

/// Raw pointer wrapper.
#[derive(Debug, Copy, Clone)]
pub struct Pointer<T>(*const T);

impl<T> Pointer<T> {
    /// Create an instance from a raw pointer.
    pub fn from_raw(raw: *const T) -> Self {
        Pointer(raw)
    }

    /// Create an instance from an address.
    pub fn from_addr(addr: usize) -> Self {
        Pointer(addr as *const _)
    }

    /// Create an instance from a reference.
    pub fn from_ref(r: &T) -> Self {
        Pointer(r as *const _)
    }

    /// Create an instance from a reference of slice.
    pub fn from_slice(slice: &[T]) -> Self {
        Pointer(slice.as_ptr())
    }

    /// Obtain the null pointer.
    pub fn null() -> Self {
        Pointer(::std::ptr::null())
    }

    /// Get the raw pointer.
    pub fn raw(&self) -> *const T {
        self.0
    }

    /// Get the mutable raw pointer
    pub fn raw_mut(&self) -> *mut T {
        self.0 as *mut _
    }

    /// Get the address.
    pub fn addr(&self) -> usize {
        self.0 as usize
    }

    /// Get the element size.
    pub fn elem_size() -> usize {
        ::std::mem::size_of::<T>()
    }

    /// Allocate memory.
    /// 
    /// Use release to release the instance.
    pub fn alloc() -> Self {
        Self::from_raw(unsafe { libc::malloc(Self::elem_size() as libc::size_t) as *const _})
    }

    /// Allocate memory for n items.
    pub fn alloc_n(n: usize) -> Self {
        Self::from_raw(unsafe { libc::malloc((Self::elem_size() * n) as libc::size_t) as *const _})
    }

    /// Deallocate memory.
    pub fn release(&self) {
        unsafe {
            libc::free(self.0 as *mut _);
        }
    }

    /// Allocate memory and initialize.
    /// 
    /// Use Pointer::delete to release the instance.
    pub fn new<G>(generator: G) -> Self
    where
        G: FnOnce() -> T
    {
        let p = Self::alloc();
        unsafe { ::std::ptr::write(p.0 as *mut _, generator()) };
        p
    }

    /// Drop and release the instance.
    pub fn delete(&self) {
        ::std::mem::drop(unsafe { ::std::ptr::read(self.0) });
        self.release();
    }

    /// Allocate memory and initialize n items.
    /// 
    /// Use Pointer::delete_n to release the instance.
    pub fn new_n<G>(n: usize, mut generator: G) -> Self
    where
        G: FnMut(usize) -> T
    {
        let headroom_size = Self::headroom_size();
        let addr = unsafe {
            let size_part = libc::malloc((headroom_size + Self::elem_size() * n) as libc::size_t) as *mut usize;
            *size_part = n;
            size_part as usize + headroom_size
        };
        let p = Pointer::<T>::from_addr(addr);
        for index in 0..n {
            unsafe { ::std::ptr::write(p.offset(index) as *mut _, generator(index)) }
        }
        p
    }

    /// Drop and release the instances.
    pub fn delete_n(&self) {
        let size = unsafe { *((self.addr() - Self::headroom_size()) as *const usize) };
        for index in 0..size {
            ::std::mem::drop(unsafe { ::std::ptr::read(self.offset(index) as *const T) });
        }
        self.release();
    }

    fn headroom_size() -> usize {
        let alignment = num::integer::lcm(::std::mem::align_of::<usize>(), ::std::mem::align_of::<T>());
        ::std::cmp::max(::std::mem::size_of::<usize>(), alignment)
    }

    /// Cast the pointing type.
    pub fn cast<U>(&self) -> Pointer<U> {
        Pointer::from_addr(self.addr())
    }

    fn offset(&self, n: usize) -> *const T {
        (self.addr() + Self::elem_size() * n) as *const _
    }

    fn ioffset(&self, n: isize) -> *const T {
        (self.addr() as isize + Self::elem_size() as isize * n) as *const _
    }

    fn rev_offset(&self, n: usize) -> *const T {
        (self.addr() - Self::elem_size() * n) as *const _
    }

    fn rev_ioffset(&self, n: isize) -> *const T {
        (self.addr() as isize - Self::elem_size() as isize * n) as *const _
    }
}

impl<T> PartialEq for Pointer<T> {
    fn eq(&self, rhs: &Self) -> bool {
        self.addr() == rhs.addr()
    }
}

impl<T> Eq for Pointer<T> {}

impl<T> PartialOrd for Pointer<T> {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        self.addr().partial_cmp(&rhs.addr())
    }
}

impl<T> Ord for Pointer<T> {
    fn cmp(&self, rhs: &Self) -> Ordering {
        self.addr().cmp(&rhs.addr())
    }
}

impl<T> Add<usize> for Pointer<T> {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        Self::from_raw(self.offset(rhs))
    }
}

impl<T> Add<Pointer<T>> for usize {
    type Output = Pointer<T>;

    fn add(self, rhs: Pointer<T>) -> Self::Output {
        Pointer::from_raw(rhs.offset(self))
    }
}

impl<T> Add<isize> for Pointer<T> {
    type Output = Self;

    fn add(self, rhs: isize) -> Self::Output {
        Self::from_raw(self.ioffset(rhs))
    }
}

impl<T> Add<Pointer<T>> for isize {
    type Output = Pointer<T>;

    fn add(self, rhs: Pointer<T>) -> Self::Output {
        Pointer::from_raw(rhs.ioffset(self))
    }
}

impl<T> AddAssign<usize> for Pointer<T> {
    fn add_assign(&mut self, rhs: usize) {
        self.0 = self.offset(rhs);
    }
}

impl<T> AddAssign<isize> for Pointer<T> {
    fn add_assign(&mut self, rhs: isize) {
        self.0 = self.ioffset(rhs);
    }
}

impl<T> Sub<usize> for Pointer<T> {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        Self::from_raw(self.rev_offset(rhs))
    }
}

impl<T> Sub<isize> for Pointer<T> {
    type Output = Self;

    fn sub(self, rhs: isize) -> Self::Output {
        Self::from_raw(self.rev_ioffset(rhs))
    }
}

impl<T> Sub<Pointer<T>> for Pointer<T> {
    type Output = isize;

    fn sub(self, rhs: Pointer<T>) -> Self::Output {
        (self.addr() as isize - rhs.addr() as isize) / Self::elem_size() as isize
    }
}

impl<T> SubAssign<usize> for Pointer<T> {
    fn sub_assign(&mut self, rhs: usize) {
        self.0 = self.rev_offset(rhs);
    }
}

impl<T> SubAssign<isize> for Pointer<T> {
    fn sub_assign(&mut self, rhs: isize) {
        self.0 = self.rev_ioffset(rhs);
    }
}

impl<T> Deref for Pointer<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0 }
    }
}

impl<T> DerefMut for Pointer<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(self.0 as *mut _) }
    }
}

impl<T> Index<usize> for Pointer<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { &*self.offset(index) }
    }
}

impl<T> Index<Pointer<T>> for usize {
    type Output = T;

    fn index(&self, pointer: Pointer<T>) -> &Self::Output {
        unsafe { &*pointer.offset(*self) }
    }
}

impl<T> Index<Pointer<T>> for isize {
    type Output = T;

    fn index(&self, pointer: Pointer<T>) -> &Self::Output {
        unsafe { &*pointer.ioffset(*self) }
    }
}

// funny C-style (?) array reference :-)
impl<T> IndexMut<usize> for Pointer<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { &mut *(self.offset(index) as *mut _) }
    }
}

impl<T> IndexMut<Pointer<T>> for usize {
    fn index_mut(&mut self, pointer: Pointer<T>) -> &mut Self::Output {
        unsafe { &mut *(pointer.offset(*self) as *mut _) }
    }
}

impl<T> IndexMut<Pointer<T>> for isize {
    fn index_mut(&mut self, pointer: Pointer<T>) -> &mut Self::Output {
        unsafe { &mut *(pointer.ioffset(*self) as *mut _) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_ops_release() {
        let mut p = Pointer::<i32>::alloc();

        *p = 5;
        assert_eq!(*p, 5);
        assert_eq!(p[0], 5);

        p[0] = 10;
        let p = p;
        assert_eq!(*p, 10);
        assert_eq!(p[0], 10);

        let next_addr = p.addr() + ::std::mem::size_of::<i32>();
        assert_eq!((p + 1usize).addr(), next_addr);
        assert_eq!((p + 1isize).addr(), next_addr);
        assert_eq!((1usize + p).addr(), next_addr);
        assert_eq!((1isize + p).addr(), next_addr);

        let mut p2 = p;
        let mut p3 = p;
        p2 += 1usize;
        p3 += 1isize;
        assert_eq!(p2.addr(), next_addr);
        assert_eq!(p2.addr(), p3.addr());
        assert_eq!((p2 - 1usize).addr(), p.addr());
        assert_eq!((p2 - 1isize).addr(), p.addr());
        assert_eq!(p - p2, -1);

        assert!(p < p2);
        assert!(p2 > p);
        assert!(p != p2);
        assert!(p2 == p3);

        p.release();
    }

    #[test]
    fn alloc_n_ops_release() {
        let mut p = Pointer::<i32>::alloc_n(3);

        for i in 0..10 {
            p[i] = i as i32 * 10;
        }
        assert_eq!(p[0], 0);
        assert_eq!(p[1], 10);
        assert_eq!(p[2], 20);

        let index = 1usize;
        let iindex = 1isize;

        assert_eq!(index[p], 10);
        assert_eq!(iindex[p], 10);

        p.release();
    }

    #[test]
    fn from_ref() {
        let n = 10;
        let p1 = Pointer::from_ref(&n);
        assert_eq!(*p1, n);

        let slice = [10, 20, 30];
        let p2 = Pointer::from_slice(&slice);
        assert_eq!(p2[0], 10);
        assert_eq!(p2[1], 20);
        assert_eq!(p2[2], 30);
    }

    #[test]
    fn cast() {
        let p_u32 = Pointer::<u32>::alloc();
        let mut p_u16 = p_u32.cast::<u16>();

        p_u16[0] = 0xC0BE;
        p_u16[1] = 0xBEEF;

        assert!((*p_u32 == 0xC0BEBEEF) || (*p_u32 == 0xBEEFC0BE));

        p_u32.release();
    }

    struct S<'a>(&'a mut i32);

    impl<'a> Drop for S<'a> {
        fn drop(&mut self) {
            *self.0 -= 100;
        }
    }

    #[test]
    fn new_delete() {
        let mut x = 1;
        {
            let p = Pointer::<S>::new(|| S(&mut x));
            assert_eq!((*p).0, &1);
            p.delete();
        }
        // make sure drop was called
        assert_eq!(x, -99);
    }

    #[test]
    fn new_n_delete_n() {
        static mut X0: i32 = 10;
        static mut X1: i32 = 20;
        static mut X2: i32 = 30;

        let p = Pointer::<S>::new_n(3, move |index| {
            let r = unsafe {
                match index {
                    0 => &mut X0,
                    1 => &mut X1,
                    _ => &mut X2,
                }
            };
            S(r)
        });
        assert_eq!(p[0].0, &10);
        assert_eq!(p[1].0, &20);
        assert_eq!(p[2].0, &30);
        p.delete_n();

        // make sure drop was called
        unsafe {
            assert_eq!(X0, -90);
            assert_eq!(X1, -80);
            assert_eq!(X2, -70);
        }
    }
}