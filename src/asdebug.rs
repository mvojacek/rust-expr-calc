
#![feature(specialization, core_intrinsics)]
use std::fmt::Debug;

pub trait AsDebug {
    fn as_debug(&self) -> &Debug;
}

impl<T> AsDebug for T {
    default fn as_debug(&self) -> &Debug {
        panic!("Debug not implemented for {}", unsafe { std::intrinsics::type_name::<T>() });
    }
}

impl<T: Debug> AsDebug for T {
    fn as_debug(&self) -> &Debug {
        self
    }
}
