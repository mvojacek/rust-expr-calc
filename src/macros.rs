#![allow(unused_macros, unused_imports)]

macro_rules! invoke_pairs {
    ($func:path => $first:expr, ) => {};
    ($func:path => $first:expr, $second:expr, $($others:expr),*) => {{
        $func($first, $second);
        invoke_pairs!($func => $second, $($others,)*);
    }};
}