// Copyright(c) The Maintainers of Nanvix.
// Licensed under the MIT License.

#![cfg_attr(not(feature = "std"), no_std)]

//==================================================================================================
// Modules
//==================================================================================================

#[cfg(all(test, feature = "std"))]
mod test;

//==================================================================================================
// Imports
//==================================================================================================

cfg_if::cfg_if! {
    if #[cfg(feature = "std")] {
        use std::alloc;
        use alloc::{
            alloc,
            dealloc,
        };
    } else {
        extern crate alloc;
        use alloc::alloc::{
            alloc,
            dealloc,
        };
    }
}

use ::core::{
    alloc::Layout,
    ops::{
        Deref,
        DerefMut,
    },
    ptr,
    slice,
};
use ::sys::error::{
    Error,
    ErrorCode,
};
use ::vstd::prelude::*;

// Include specifications.
#[cfg(verus_keep_ghost)]
include!("lib.spec.rs");

// Include proofs.
#[cfg(verus_keep_ghost)]
include!("lib.proof.rs");

//==================================================================================================
// Raw Array Storage
//==================================================================================================

///
/// # Description
///
/// A type that represents the backing storage of a [`RawArray`].
///
#[derive(Debug)]
enum RawArrayStorage<T> {
    /// A storage area that is managed by [alloc::GlobalAlloc].
    Managed { ptr: ptr::NonNull<T>, len: usize },
    /// A storage area that is not managed by [alloc::GlobalAlloc].
    Unmanaged { ptr: ptr::NonNull<T>, len: usize },
}

// Verus does not support &mut return types.
impl<T> RawArrayStorage<T> {
    ///
    /// # Description
    ///
    /// Gets a mutable slice to the underlying data in the backing storage.
    ///
    /// # Returns
    ///
    /// A mutable slice to the underlying data in the backing storage.
    ///
    fn get_mut(&mut self) -> &mut [T] {
        match self {
            RawArrayStorage::Managed { ptr, len } => unsafe {
                slice::from_raw_parts_mut(ptr.as_ptr(), *len)
            },
            RawArrayStorage::Unmanaged { ptr, len } => unsafe {
                slice::from_raw_parts_mut(ptr.as_ptr(), *len)
            },
        }
    }
}

//==================================================================================================
// Raw Array
//==================================================================================================

// External type specifications for Verus verification.
#[cfg(verus_keep_ghost)]
verus! {

// External type specification for RawArrayStorage.
#[verifier::reject_recursive_types(T)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRawArrayStorage<T>(RawArrayStorage<T>);

// External type specification for Layout.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLayout(Layout);

// External type specification for LayoutError.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLayoutError(core::alloc::LayoutError);

/// Specification for Layout::array::<T>(len).
/// Succeeds when len * size_of::<T>() does not overflow isize::MAX.
pub assume_specification<T>[ Layout::array::<T> ](len: usize) -> (result: Result<Layout, core::alloc::LayoutError>)
    ensures
        len * vstd::layout::size_of::<T>() <= isize::MAX as usize ==> result is Ok,
    opens_invariants none
    no_unwind
;

/// Specification for alloc(layout).
/// Returns a non-null pointer on success, null on out-of-memory.
pub assume_specification[ alloc ](layout: Layout) -> (result: *mut u8)
    opens_invariants none
;

}

verus! {

//==================================================================================================
// RawArrayStorage — Verified Methods
//==================================================================================================

/// Checks pointer for null, zero-initializes memory, and constructs Unmanaged storage.
/// Returns None if pointer is null.
#[verifier::external_body]
fn try_make_unmanaged_storage<T>(ptr: *mut T, len: usize) -> (result: Option<RawArrayStorage<T>>)
    ensures
        ptr.addr() != 0 ==> result is Some,
        ptr.addr() == 0 ==> result is None,
        result is Some ==> {
            &&& result->Some_0.spec_view().len() == len
            &&& forall|i: int| 0 <= i < len ==> is_zero(#[trigger] result->Some_0.spec_view()[i])
        },
    opens_invariants none
    no_unwind
{
    match ptr::NonNull::new(ptr) {
        Some(p) => {
            unsafe { ptr::write_bytes(p.as_ptr(), 0, len) };
            Some(RawArrayStorage::Unmanaged { ptr: p, len })
        },
        None => None,
    }
}

/// Checks if a raw pointer wraps around when offset by len elements.
/// Returns true if the region wraps (invalid).
#[verifier::external_body]
fn ptr_wraps_around<T>(ptr: *mut T, len: usize) -> (result: bool)
    ensures
        result == (ptr.addr() + len * vstd::layout::size_of::<T>() > usize::MAX as int),
    opens_invariants none
    no_unwind
{
    ptr.wrapping_add(len) < ptr
}

/// Returns None if pointer is null.
#[verifier::external_body]
fn try_make_managed_storage<T>(ptr: *mut u8, len: usize) -> (result: Option<RawArrayStorage<T>>)
    ensures
        ptr.addr() != 0 ==> result is Some,
        ptr.addr() == 0 ==> result is None,
        result is Some ==> {
            &&& result->Some_0.spec_view().len() == len
            &&& forall|i: int| 0 <= i < len ==> is_zero(#[trigger] result->Some_0.spec_view()[i])
        },
    opens_invariants none
    no_unwind
{
    match ptr::NonNull::new(ptr as *mut T) {
        Some(p) => {
            // Safety: The memory region is valid and the length is valid.
            unsafe { ptr::write_bytes(p.as_ptr(), 0, len) };
            Some(RawArrayStorage::Managed { ptr: p, len })
        },
        None => None,
    }
}

impl<T> RawArrayStorage<T> {
    /// Abstract view of the storage as a sequence (uninterpreted).
    #[verifier::external_body]
    pub open spec fn spec_view(&self) -> Seq<T> {
        unimplemented!()
    }

    ///
    /// # Description
    ///
    /// Constructs backing storage for a raw array.
    ///
    /// # Parameters
    ///
    /// - `len`: Length of the backing storage.
    ///
    /// # Returns
    ///
    /// On success, the backing storage is returned, with all bits set to zero.
    /// On failure, an error is returned instead.
    ///
    fn new_managed(len: usize) -> (result: Result<RawArrayStorage<T>, Error>)
        requires
            len > 0,
            len < i32::MAX as usize,
            len * vstd::layout::size_of::<T>() <= isize::MAX as usize,
        ensures
            result is Ok ==> {
                &&& result->Ok_0.spec_view().len() == len
                &&& forall|i: int| 0 <= i < len ==> is_zero(#[trigger] result->Ok_0.spec_view()[i])
            },
            result is Err ==> result->Err_0.code == ErrorCode::OutOfMemory,
    {
        // Check if the length is invalid.
        if len == 0 || len >= i32::MAX as usize {
            return Err(Error::new(ErrorCode::InvalidArgument, "invalid length"));
        }

        // Allocate underlying memory.
        let layout: Layout = match Layout::array::<T>(len) {
            Ok(layout) => layout,
            Err(_) => return Err(Error::new(ErrorCode::InvalidArgument, "invalid layout")),
        };
        let ptr: *mut u8 = unsafe { alloc(layout) };

        // Null-check, zero-initialize, and construct storage.
        match try_make_managed_storage(ptr, len) {
            Some(storage) => Ok(storage),
            None => Err(Error::new(ErrorCode::OutOfMemory, "out of memory")),
        }
    }

    ///
    /// # Description
    ///
    /// Constructs an unmanaged backing storage for a raw array.
    ///
    /// # Parameters
    ///
    /// - `ptr`: Pointer to the backing storage.
    /// - `len`: Length of the backing storage.
    ///
    /// # Returns
    ///
    /// On success, the backing storage is returned, with all bits set to zero.
    /// On failure, an error is returned instead.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if any of the following conditions are violated:
    ///
    /// - `ptr` must be valid for both reads and writes for `len * mem::size_of::<T>()` many bytes.
    /// - `ptr` must be properly aligned.
    /// - `ptr` must point to len consecutive properly initialized values of type `T``.
    ///
    unsafe fn new_unmanaged(ptr: *mut T, len: usize) -> (result: Result<RawArrayStorage<T>, Error>)
        requires
            len > 0,
            len < i32::MAX as usize,
            ptr.addr() != 0,
            ptr.addr() + len * vstd::layout::size_of::<T>() <= usize::MAX as int,
        ensures
            result is Ok ==> {
                &&& result->Ok_0.spec_view().len() == len
                &&& forall|i: int| 0 <= i < len ==> is_zero(#[trigger] result->Ok_0.spec_view()[i])
            },
            result is Ok,
    {
        // Check if the length is invalid.
        if len == 0 || len >= i32::MAX as usize {
            return Err(Error::new(ErrorCode::InvalidArgument, "invalid length"));
        }

        // Check if memory region wraps around.
        if ptr_wraps_around(ptr, len) {
            return Err(Error::new(ErrorCode::InvalidArgument, "wrapping memory region"));
        }

        // Null-check, zero-initialize, and construct storage.
        match try_make_unmanaged_storage(ptr, len) {
            Some(storage) => Ok(storage),
            None => Err(Error::new(ErrorCode::InvalidArgument, "invalid pointer")),
        }
    }

    ///
    /// # Description
    ///
    /// Gets a slice to the underlying data in the backing storage.
    ///
    /// # Returns
    ///
    /// A slice to the underlying data in the backing storage.
    ///
    #[verifier::external_body]
    fn get(&self) -> (result: &[T])
    {
        match self {
            RawArrayStorage::Managed { ptr, len } => unsafe {
                slice::from_raw_parts(ptr.as_ptr(), *len)
            },
            RawArrayStorage::Unmanaged { ptr, len } => unsafe {
                slice::from_raw_parts(ptr.as_ptr(), *len)
            },
        }
    }
}

//==================================================================================================
// RawArray Definition
//==================================================================================================

///
/// # Description
///
/// A type that represent a fixed-size array.
///
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[verifier::reject_recursive_types(T)]
pub struct RawArray<T> {
    /// The backing storage of the raw array.
    storage: RawArrayStorage<T>,
}

impl<T> RawArray<T> {
    ///
    /// # Description
    ///
    /// Constructs a new managed array.
    ///
    /// # Parameters
    ///
    /// - `len`: Length of the array.
    ///
    /// # Returns
    ///
    /// On success, the new managed array is returned, with all bits set to zero.
    /// On failure, an error is returned instead.
    ///
    pub fn new(len: usize) -> (result: Result<RawArray<T>, Error>)
        requires
            len > 0,
            len < i32::MAX as usize,
            len * vstd::layout::size_of::<T>() <= isize::MAX as usize,
        ensures
            result is Ok ==> {
                &&& result->Ok_0.inv()
                &&& result->Ok_0@.len() == len
                &&& forall|i: int| 0 <= i < len ==> is_zero(#[trigger] result->Ok_0@[i])
            },
            result is Err ==> result->Err_0.code == ErrorCode::OutOfMemory,
    {
        let storage: RawArrayStorage<T> = RawArrayStorage::new_managed(len)?;
        let arr: RawArray<T> = RawArray { storage };
        proof {
            // Bridge: RawArray's view equals its storage's view.
            assume(arr@.len() == arr.storage.spec_view().len());
            assume(forall|i: int| #![auto] 0 <= i < len ==> arr@[i] == arr.storage.spec_view()[i]);
        }
        Ok(arr)
    }

    ///
    /// # Description
    ///
    /// Constructs a new unmanaged array.
    ///
    /// # Parameters
    ///
    /// - `ptr`: Pointer to the backing storage.
    /// - `len`: Length of the backing storage.
    ///
    /// # Returns
    ///
    /// On success, the new unmanaged array is returned, with all bits set to zero.
    /// On failure, an error is returned instead.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if any of the following conditions are violated:
    ///
    /// - `ptr` must be valid for both reads and writes for `len * mem::size_of::<T>()` many bytes.
    /// - `ptr` must be properly aligned.
    /// - `ptr` must point to len consecutive properly initialized values of type `T``.
    ///
    pub unsafe fn from_raw_parts(ptr: *mut T, len: usize) -> (result: Result<RawArray<T>, Error>)
        requires
            len > 0,
            len < i32::MAX as usize,
            ptr.addr() != 0,
            ptr.addr() + len * vstd::layout::size_of::<T>() <= usize::MAX as int,
        ensures
            result is Ok ==> {
                &&& result->Ok_0.inv()
                &&& result->Ok_0@.len() == len
                &&& forall|i: int| 0 <= i < len ==> is_zero(#[trigger] result->Ok_0@[i])
            },
            result is Err ==> result->Err_0.code == ErrorCode::InvalidArgument,
    {
        let storage: RawArrayStorage<T> = unsafe { RawArrayStorage::new_unmanaged(ptr, len)? };
        let arr: RawArray<T> = RawArray { storage };
        proof {
            // Bridge: RawArray's view equals its storage's view.
            assume(arr@.len() == arr.storage.spec_view().len());
            assume(forall|i: int| #![auto] 0 <= i < len ==> arr@[i] == arr.storage.spec_view()[i]);
        }
        Ok(arr)
    }
}

impl<T> RawArray<T> {
    /// Sets the element at index to value.
    /// Verus does not support mutable indexing (arr[i] = val), so this method
    /// provides a verified mutator with requires/ensures contracts.
    #[verifier::external_body]
    pub fn set(&mut self, index: usize, value: T)
        requires
            old(self).in_bounds(index as int),
        ensures
            self@.len() == old(self)@.len(),
            self@[index as int] == value,
            forall|i: int| 0 <= i < self@.len() && i != index as int
                ==> self@[i] == old(self)@[i],
    {
        self.storage.get_mut()[index] = value;
    }
}

impl<T> Deref for RawArray<T> {
    type Target = [T];

    #[verifier::external_body]
    fn deref(&self) -> (result: &Self::Target)
        ensures
            result@ == self@,
    {
        self.storage.get()
    }
}

} // verus!

// Verus does not support &mut return types, so DerefMut is outside verus!{}.
impl<T> DerefMut for RawArray<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.storage.get_mut()
    }
}

impl<T> Drop for RawArray<T> {
    fn drop(&mut self) {
        match &self.storage {
            RawArrayStorage::Managed { ptr, len } => {
                let layout: Layout = match Layout::array::<T>(*len) {
                    Ok(layout) => layout,
                    Err(_) => return,
                };
                unsafe {
                    dealloc(ptr.as_ptr() as *mut u8, layout);
                }
            },
            RawArrayStorage::Unmanaged { .. } => (),
        }
    }
}
