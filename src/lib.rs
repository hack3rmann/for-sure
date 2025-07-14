#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]

use Almost::{Nil, Value};
use core::{
    fmt,
    iter::FusedIterator,
    mem,
    ops::{Deref, DerefMut},
    pin::Pin,
    slice,
};

pub mod prelude {
    pub use super::Almost::{self, Nil, Value};
}

/// A type similar to [`Option`] but with [`Deref<Target = T>`] implementation.
/// See crate-level documentation for more info.
#[derive(PartialEq, Default, PartialOrd, Eq, Ord, Copy, Hash)]
pub enum Almost<T> {
    #[default]
    Nil,
    Value(T),
}

impl<T> Almost<T> {
    /// Returns `true` if the almost is a [`Value`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<u32> = Value(2);
    /// assert!(Almost::is_value(&x));
    ///
    /// let x: Almost<u32> = Nil;
    /// assert!(Almost::is_nil(&x));
    /// ```
    #[must_use = "if you intended to assert that this has a value, consider `Almost::unwrap()` instead"]
    #[inline]
    pub const fn is_value(this: &Self) -> bool {
        matches!(this, Value(..))
    }

    /// Returns `true` if the almost is a [`Value`] and the value inside of it matches a predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<u32> = Value(2);
    /// assert!(Almost::is_value_and(x, |x| x > 1));
    ///
    /// let x: Almost<u32> = Value(0);
    /// assert!(!Almost::is_value_and(x, |x| x > 1));
    ///
    /// let x: Almost<u32> = Nil;
    /// assert!(!Almost::is_value_and(x, |x| x > 1));
    ///
    /// let x: Almost<String> = Value("ownership".to_string());
    /// assert!(Almost::is_value_and(Almost::as_ref(&x), |x| x.len() > 1));
    /// println!("still alive {:?}", x);
    /// ```
    #[must_use]
    #[inline]
    pub fn is_value_and(this: Self, f: impl FnOnce(T) -> bool) -> bool {
        match this {
            Nil => false,
            Value(x) => f(x),
        }
    }

    /// Returns `true` if the almost is a [`Value`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<u32> = Value(2);
    /// assert!(!Almost::is_nil(&x));
    ///
    /// let x: Almost<u32> = Nil;
    /// assert!(Almost::is_nil(&x));
    /// ```
    #[must_use = "if you intended to assert that this doesn't have a value, consider \
                  wrapping this in an `assert!()` instead"]
    #[inline]
    pub const fn is_nil(this: &Self) -> bool {
        matches!(this, Nil)
    }

    /// Returns `true` if the almost is a [`Value`] or the value inside of it matches a predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<u32> = Value(2);
    /// assert!(Almost::is_nil_or(x, |x| x > 1));
    ///
    /// let x: Almost<u32> = Value(0);
    /// assert!(!Almost::is_nil_or(x, |x| x > 1));
    ///
    /// let x: Almost<u32> = Nil;
    /// assert!(Almost::is_nil_or(x, |x| x > 1));
    ///
    /// let x: Almost<String> = Value("ownership".to_string());
    /// assert!(Almost::is_nil_or(Almost::as_ref(&x), |x| x.len() > 1));
    /// println!("still alive {:?}", x);
    /// ```
    #[must_use]
    #[inline]
    pub fn is_nil_or(this: Self, f: impl FnOnce(T) -> bool) -> bool {
        match this {
            Nil => true,
            Value(x) => f(x),
        }
    }

    /// Converts from `&Almost<T>` to `Almost<&T>`
    #[inline]
    pub const fn as_ref(this: &Self) -> Almost<&T> {
        match this {
            Nil => Nil,
            Value(x) => Value(x),
        }
    }

    /// Converts from `&mut Almost<T>` to `Almost<&mut T>`
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x = Value(2);
    /// match Almost::as_mut(&mut x) {
    ///     Value(v) => *v = 42,
    ///     Nil => {},
    /// }
    /// assert_eq!(x, Value(42));
    /// ```
    #[inline]
    pub const fn as_mut(this: &mut Self) -> Almost<&mut T> {
        match this {
            Nil => Nil,
            Value(x) => Value(x),
        }
    }

    /// Converts from `Pin<&Almost<T>>` to `Almost<Pin<&T>>`
    #[inline]
    pub const fn as_pin_ref(this: Pin<&Self>) -> Almost<Pin<&T>> {
        match Self::as_ref(Pin::get_ref(this)) {
            Value(x) => Value(unsafe { Pin::new_unchecked(x) }),
            Nil => Nil,
        }
    }

    /// Converts from `Pin<&mut Almost<T>>` to `Almost<Pin<&mut T>>`
    #[inline]
    pub const fn as_pin_mut(this: Pin<&mut Self>) -> Almost<Pin<&mut T>> {
        match Self::as_mut(unsafe { Pin::get_unchecked_mut(this) }) {
            Value(x) => Value(unsafe { Pin::new_unchecked(x) }),
            Nil => Nil,
        }
    }

    /// Returns a slice of the contained value, if any. If this is [`Nil`], an
    /// empty slice is returned. This can be useful to have a single type of
    /// iterator over an [`Almost`] or slice.
    ///
    /// Note: Should you have an `Almost<&T>` and wish to get a slice of `T`,
    /// you can unpack it via `Almost::map_or(opt, &[], std::slice::from_ref)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// assert_eq!(Almost::as_slice(&Value(1234)), &[1234][..]);
    /// assert_eq!(Almost::as_slice(&Nil::<i32>), &[][..]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_slice(this: &Self) -> &[T] {
        match this {
            Value(value) => unsafe { slice::from_raw_parts(&raw const *value, 1) },
            Nil => &[],
        }
    }

    /// Returns a mutable slice of the contained value, if any. If this is [`Nil`], an
    /// empty slice is returned. This can be useful to have a single type of
    /// iterator over an [`Almost`] or slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// assert_eq!(Almost::as_slice_mut(&mut Value(1234)), &mut [1234][..]);
    /// assert_eq!(Almost::as_slice_mut(&mut Nil::<i32>), &mut [][..]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_slice_mut(this: &mut Self) -> &mut [T] {
        match this {
            Value(value) => unsafe { slice::from_raw_parts_mut(&raw mut *value, 1) },
            Nil => &mut [],
        }
    }

    /// Returns the contained [`Value`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a [`Nil`] with a custom panic message provided by
    /// `msg`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value("value");
    /// assert_eq!(Almost::expect(x, "fruits are healthy"), "value");
    /// ```
    ///
    /// ```should_panic
    /// # use for_sure::prelude::*;
    /// let x: Almost<&str> = Nil;
    /// Almost::expect(x, "fruits are healthy"); // panics with `fruits are healthy`
    /// ```
    ///
    /// # Recommended Message Style
    ///
    /// We recommend that `expect` messages are used to describe the reason you
    /// _expect_ the `Almost` should be `Value`.
    ///
    /// ```should_panic
    /// # use for_sure::prelude::*;
    /// # let slice: &[u8] = &[];
    /// let maybe_item = Almost::from_option(slice.get(0));
    /// let item = Almost::expect(maybe_item, "slice should not be empty");
    /// ```
    #[inline]
    #[track_caller]
    pub fn expect(this: Self, msg: &str) -> T {
        match this {
            Value(x) => x,
            Nil => panic!("{}", msg),
        }
    }

    /// Returns the contained [`Value`] value, consuming the `self` value.
    ///
    /// Because this function may panic, its use is generally discouraged.
    /// Panics are meant for unrecoverable errors, and may abort the entire program.
    ///
    /// Instead, prefer to use pattern matching and handle the [`Nil`]
    /// case explicitly, or call [`Almost::unwrap_or`], [`Almost::unwrap_or_else`], or
    /// [`Almost::unwrap_or_default`].
    ///
    /// # Panics
    ///
    /// Panics if the self value equals [`Nil`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value("air");
    /// assert_eq!(Almost::unwrap(x), "air");
    /// ```
    ///
    /// ```should_panic
    /// # use for_sure::prelude::*;
    /// let x: Almost<&str> = Nil;
    /// assert_eq!(Almost::unwrap(x), "air"); // fails
    /// ```
    #[inline(always)]
    #[track_caller]
    pub fn unwrap(this: Self) -> T {
        match this {
            Value(x) => x,
            Nil => panic!("called `Almost::unwrap()` on a `Nil` value"),
        }
    }

    /// Returns the contained [`Value`] value or a provided default.
    ///
    /// Arguments passed to `unwrap_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`Almost::unwrap_or_else`],
    /// which is lazily evaluated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// assert_eq!(Almost::unwrap_or(Value("car"), "bike"), "car");
    /// assert_eq!(Almost::unwrap_or(Nil, "bike"), "bike");
    /// ```
    #[inline]
    pub fn unwrap_or(this: Self, default: T) -> T {
        match this {
            Value(x) => x,
            Nil => default,
        }
    }

    /// Returns the contained [`Value`] value or computes it from a closure.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let k = 10;
    /// assert_eq!(Almost::unwrap_or_else(Value(4), || 2 * k), 4);
    /// assert_eq!(Almost::unwrap_or_else(Nil, || 2 * k), 20);
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap_or_else(this: Self, f: impl FnOnce() -> T) -> T {
        match this {
            Value(x) => x,
            Nil => f(),
        }
    }

    /// Returns the contained [`Value`] value or a default.
    ///
    /// Consumes the `self` argument then, if [`Value`], returns the contained
    /// value, otherwise if [`Nil`], returns the [default value] for that
    /// type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<u32> = Nil;
    /// let y: Almost<u32> = Value(12);
    ///
    /// assert_eq!(Almost::unwrap_or_default(x), 0);
    /// assert_eq!(Almost::unwrap_or_default(y), 12);
    /// ```
    ///
    /// [default value]: Default::default
    #[inline]
    pub fn unwrap_or_default(this: Self) -> T
    where
        T: Default,
    {
        match this {
            Value(x) => x,
            Nil => T::default(),
        }
    }

    /// Returns the contained [`Value`] value, consuming the `self` value,
    /// without checking that the value is not [`Value`].
    ///
    /// # Safety
    ///
    /// Calling this method on [`Nil`] is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value("air");
    /// assert_eq!(unsafe { Almost::unwrap_unchecked(x) }, "air");
    /// ```
    ///
    /// ```no_run
    /// # use for_sure::prelude::*;
    /// let x: Almost<&str> = Nil;
    /// assert_eq!(unsafe { Almost::unwrap_unchecked(x) }, "air"); // Undefined behavior!
    /// ```
    #[inline]
    #[track_caller]
    pub unsafe fn unwrap_unchecked(this: Self) -> T {
        match this {
            Value(x) => x,
            Nil => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Maps an `Almost<T>` to `Almost<U>` by applying a function to a contained value (if `Value`) or returns `Nil` (if `Nil`).
    ///
    /// # Examples
    ///
    /// Calculates the length of an `Almost<String>` as an `Almost<usize>` consuming the original:
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let maybe_some_string = Value(String::from("Hello, World!"));
    /// // `Almost::map` takes self *by value*, consuming `maybe_some_string`
    /// let maybe_some_len = Almost::map(maybe_some_string, |s| s.len());
    /// assert_eq!(maybe_some_len, Value(13));
    ///
    /// let x: Almost<&str> = Nil;
    /// assert_eq!(Almost::map(x, |s| s.len()), Nil);
    /// ```
    #[inline]
    pub fn map<U>(this: Self, f: impl FnOnce(T) -> U) -> Almost<U> {
        match this {
            Value(x) => Value(f(x)),
            Nil => Nil,
        }
    }

    /// Calls a function with a reference to the contained value if Value.
    ///
    /// Returns the original almost.
    #[inline]
    pub fn inspect(this: Self, f: impl FnOnce(&T)) -> Self {
        match this {
            Value(x) => {
                f(&x);
                Value(x)
            }
            Nil => Nil,
        }
    }

    /// Returns the provided default result (if nil),
    /// or applies a function to the contained value (if any).
    ///
    /// Arguments passed to `map_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`Almost::map_or_else`],
    /// which is lazily evaluated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value("foo");
    /// assert_eq!(Almost::map_or(x, 42, |v| v.len()), 3);
    ///
    /// let x: Almost<&str> = Nil;
    /// assert_eq!(Almost::map_or(x, 42, |v| v.len()), 42);
    /// ```
    #[inline]
    pub fn map_or<U>(this: Self, default: U, f: impl FnOnce(T) -> U) -> U {
        match this {
            Value(x) => f(x),
            Nil => default,
        }
    }

    /// Computes a default function result (if nill), or
    /// applies a different function to the contained value (if any).
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let k = 21;
    ///
    /// let x = Value("foo");
    /// assert_eq!(Almost::map_or_else(x, || 2 * k, |v| v.len()), 3);
    ///
    /// let x: Almost<&str> = Nil;
    /// assert_eq!(Almost::map_or_else(x, || 2 * k, |v| v.len()), 42);
    /// ```
    #[inline]
    pub fn map_or_else<U>(this: Self, default: impl FnOnce() -> U, f: impl FnOnce(T) -> U) -> U {
        match this {
            Value(x) => f(x),
            Nil => default(),
        }
    }

    /// Transforms the `Almost<T>` into a [`Result<T, E>`], mapping [`Value(v)`] to
    /// [`Ok(v)`] and [`Nil`] to [`Err(err)`].
    ///
    /// Arguments passed to `ok_or` are eagerly evaluated; if you are passing the
    /// result of a function call, it is recommended to use [`ok_or_else`], which is
    /// lazily evaluated.
    ///
    /// [`Ok(v)`]: Ok
    /// [`Err(err)`]: Err
    /// [`Value(v)`]: Value
    /// [`ok_or_else`]: Almost::ok_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value("foo");
    /// assert_eq!(Almost::ok_or(x, 0), Ok("foo"));
    ///
    /// let x: Almost<&str> = Nil;
    /// assert_eq!(Almost::ok_or(x, 0), Err(0));
    /// ```
    #[inline]
    pub fn ok_or<E>(this: Self, error: E) -> Result<T, E> {
        match this {
            Value(x) => Ok(x),
            Nil => Err(error),
        }
    }

    /// Transforms the `Almost<T>` into a [`Result<T, E>`], mapping [`Value(v)`] to
    /// [`Ok(v)`] and [`Nil`] to [`Err(err())`].
    ///
    /// [`Ok(v)`]: Ok
    /// [`Err(err())`]: Err
    /// [`Value(v)`]: Value
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value("foo");
    /// assert_eq!(Almost::ok_or_else(x, || 0), Ok("foo"));
    ///
    /// let x: Almost<&str> = Nil;
    /// assert_eq!(Almost::ok_or_else(x, || 0), Err(0));
    /// ```
    #[inline]
    pub fn ok_or_else<E>(this: Self, error: impl FnOnce() -> E) -> Result<T, E> {
        match this {
            Value(x) => Ok(x),
            Nil => Err(error()),
        }
    }

    /// Converts from `Almost<T>` (or `&Almost<T>`) to `Almost<&T::Target>`.
    ///
    /// Leaves the original [`Almost`] in-place, creating a new one with a reference
    /// to the original one, additionally coercing the contents via [`Deref`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<String> = Value("hey".to_owned());
    /// assert_eq!(Almost::as_deref(&x), Value("hey"));
    ///
    /// let x: Almost<String> = Nil;
    /// assert_eq!(Almost::as_deref(&x), Nil);
    /// ```
    #[inline]
    pub fn as_deref(this: &Self) -> Almost<&<T as Deref>::Target>
    where
        T: Deref,
    {
        match this {
            Value(x) => Value(x.deref()),
            Nil => Nil,
        }
    }

    /// Converts from `Almost<T>` (or `&mut Almost<T>`) to `Almost<&mut T::Target>`.
    ///
    /// Leaves the original `Almost` in-place, creating a new one containing a mutable reference to
    /// the inner type's [`Deref::Target`] type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x: Almost<String> = Nil;
    /// assert_eq!(Almost::as_deref_mut(&mut x), Nil);
    /// ```
    #[inline]
    pub fn as_deref_mut(this: &mut Self) -> Almost<&mut <T as Deref>::Target>
    where
        T: DerefMut,
    {
        match this {
            Value(x) => Value(x.deref_mut()),
            Nil => Nil,
        }
    }

    /// Converts `Almost<T>` into an `Option<T>`
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<i32> = Value(42);
    /// let x: Option<i32> = Almost::into_option(x);
    /// assert_eq!(x, Some(42));
    ///
    /// let y = Nil::<i32>;
    /// let y: Option<i32> = Almost::into_option(y);
    /// assert_eq!(y, None);
    /// ```
    #[inline]
    pub fn into_option(this: Self) -> Option<T> {
        match this {
            Value(x) => Some(x),
            Nil => None,
        }
    }

    /// Returns an iterator over the possibly contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value(4);
    /// assert_eq!(Almost::iter(&x).next(), Some(&4));
    ///
    /// let x: Almost<u32> = Nil;
    /// assert_eq!(Almost::iter(&x).next(), None);
    /// ```
    #[inline]
    pub fn iter(this: &Self) -> Iter<'_, T> {
        Iter {
            value: Almost::into_option(Self::as_ref(this)),
        }
    }

    /// Returns a mutable iterator over the possibly contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x = Value(4);
    /// match Almost::iter_mut(&mut x).next() {
    ///     Some(v) => *v = 42,
    ///     None => {},
    /// }
    /// assert_eq!(x, Value(42));
    ///
    /// let mut x: Almost<u32> = Nil;
    /// assert_eq!(Almost::iter_mut(&mut x).next(), None);
    /// ```
    #[inline]
    pub fn iter_mut(this: &mut Self) -> IterMut<'_, T> {
        IterMut {
            value: Almost::into_option(Self::as_mut(this)),
        }
    }

    /// Returns [`Nil`] if the option is [`Nil`], otherwise returns `other`.
    ///
    /// Arguments passed to `and` are eagerly evaluated; if you are passing the
    /// result of a function call, it is recommended to use [`and_then`], which is
    /// lazily evaluated.
    ///
    /// [`and_then`]: Almost::and_then
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value(2);
    /// let y: Almost<&str> = Nil;
    /// assert_eq!(Almost::and(x, y), Nil);
    ///
    /// let x: Almost<u32> = Nil;
    /// let y = Value("foo");
    /// assert_eq!(Almost::and(x, y), Nil);
    ///
    /// let x = Value(2);
    /// let y = Value("foo");
    /// assert_eq!(Almost::and(x, y), Value("foo"));
    ///
    /// let x: Almost<u32> = Nil;
    /// let y: Almost<&str> = Nil;
    /// assert_eq!(Almost::and(x, y), Nil);
    /// ```
    #[inline]
    pub fn and<U>(this: Self, other: Almost<U>) -> Almost<U> {
        match this {
            Nil => Nil,
            Value(_) => other,
        }
    }

    /// Returns [`Nil`] if the option is [`Nil`], otherwise calls `f` with the
    /// wrapped value and returns the result.
    ///
    /// Some languages call this operation flatmap.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// fn sq_then_to_string(x: u32) -> Almost<String> {
    ///     x.checked_mul(x).map(|sq| sq.to_string()).into()
    /// }
    ///
    /// assert_eq!(Almost::and_then(Value(2), sq_then_to_string), Value(4.to_string()));
    /// assert_eq!(Almost::and_then(Value(1_000_000), sq_then_to_string), Nil); // overflowed!
    /// assert_eq!(Almost::and_then(Nil, sq_then_to_string), Nil);
    /// ```
    #[doc(alias = "flatmap")]
    #[inline]
    pub fn and_then<U>(this: Self, other: impl FnOnce(T) -> Almost<U>) -> Almost<U> {
        match this {
            Nil => Nil,
            Value(x) => other(x),
        }
    }

    /// Returns [`Nil`] if the option is [`Nil`], otherwise calls `predicate`
    /// with the wrapped value and returns:
    ///
    /// - [`Value(t)`] if `predicate` returns `true` (where `t` is the wrapped
    ///   value), and
    /// - [`Nil`] if `predicate` returns `false`.
    ///
    /// This function works similar to [`Iterator::filter()`]. You can imagine
    /// the `Almost<T>` being an iterator over one or zero elements. `filter()`
    /// lets you decide which elements to keep.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// fn is_even(n: &i32) -> bool {
    ///     n % 2 == 0
    /// }
    ///
    /// assert_eq!(Almost::filter(Nil, is_even), Nil);
    /// assert_eq!(Almost::filter(Value(3), is_even), Nil);
    /// assert_eq!(Almost::filter(Value(4), is_even), Value(4));
    /// ```
    ///
    /// [`Value(t)`]: Value
    #[inline]
    pub fn filter(this: Self, do_get: impl FnOnce(&T) -> bool) -> Self {
        if let Value(x) = this
            && do_get(&x)
        {
            return Value(x);
        }

        Nil
    }

    /// Returns the almost if it contains a value, otherwise returns `other`.
    ///
    /// Arguments passed to `or` are eagerly evaluated; if you are passing the
    /// result of a function call, it is recommended to use [`or_else`], which is
    /// lazily evaluated.
    ///
    /// [`or_else`]: Almost::or_else
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value(2);
    /// let y = Nil;
    /// assert_eq!(Almost::or(x, y), Value(2));
    ///
    /// let x = Nil;
    /// let y = Value(100);
    /// assert_eq!(Almost::or(x, y), Value(100));
    ///
    /// let x = Value(2);
    /// let y = Value(100);
    /// assert_eq!(Almost::or(x, y), Value(2));
    ///
    /// let x: Almost<u32> = Nil;
    /// let y = Nil;
    /// assert_eq!(Almost::or(x, y), Nil);
    /// ```
    #[inline]
    pub fn or(this: Self, other: Self) -> Self {
        match this {
            Nil => other,
            Value(x) => Value(x),
        }
    }

    /// Returns the almost if it contains a value, otherwise calls `f` and
    /// returns the result.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// fn nobody() -> Almost<&'static str> { Nil }
    /// fn vikings() -> Almost<&'static str> { Value("vikings") }
    ///
    /// assert_eq!(Almost::or_else(Value("barbarians"), vikings), Value("barbarians"));
    /// assert_eq!(Almost::or_else(Nil, vikings), Value("vikings"));
    /// assert_eq!(Almost::or_else(Nil, nobody), Nil);
    /// ```
    #[inline]
    pub fn or_else(this: Self, f: impl FnOnce() -> Self) -> Self {
        match this {
            Nil => f(),
            Value(x) => Value(x),
        }
    }

    /// Returns [`Value`] if exactly one of `self`, `other` is [`Value`], otherwise returns [`Nil`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value(2);
    /// let y: Almost<u32> = Nil;
    /// assert_eq!(Almost::xor(x, y), Value(2));
    ///
    /// let x: Almost<u32> = Nil;
    /// let y = Value(2);
    /// assert_eq!(Almost::xor(x, y), Value(2));
    ///
    /// let x = Value(2);
    /// let y = Value(2);
    /// assert_eq!(Almost::xor(x, y), Nil);
    ///
    /// let x: Almost<u32> = Nil;
    /// let y: Almost<u32> = Nil;
    /// assert_eq!(Almost::xor(x, y), Nil);
    /// ```
    #[inline]
    pub fn xor(this: Self, other: Self) -> Self {
        match (this, other) {
            (Value(x), Nil) | (Nil, Value(x)) => Value(x),
            (Value(_), Value(_)) | (Nil, Nil) => Nil,
        }
    }

    /// Inserts `value` into the almost, then returns a mutable reference to it.
    ///
    /// If the almost already contains a value, the old value is dropped.
    ///
    /// See also [`Almost::get_or_insert`], which doesn't update the value if
    /// the option already contains [`Value`].
    ///
    /// # Example
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut almost = Nil;
    /// let val = Almost::insert(&mut almost, 1);
    /// assert_eq!(*val, 1);
    /// assert_eq!(Almost::unwrap(almost), 1);
    ///
    /// let val = Almost::insert(&mut almost, 2);
    /// assert_eq!(*val, 2);
    /// *val = 3;
    /// assert_eq!(Almost::unwrap(almost), 3);
    /// ```
    #[must_use = "if you intended to set a value, consider assignment instead"]
    #[inline]
    pub fn insert(this: &mut Self, value: T) -> &mut T {
        *this = Value(value);
        // Safety: the code above just filled the option
        unsafe { Almost::unwrap_unchecked(Almost::as_mut(this)) }
    }

    /// Inserts `value` into the almost if it is [`Nil`], then
    /// returns a mutable reference to the contained value.
    ///
    /// See also [`Almost::insert`], which updates the value even if
    /// the option already contains [`Almost`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x = Nil;
    ///
    /// {
    ///     let y: &mut u32 = Almost::get_or_insert(&mut x, 5);
    ///     assert_eq!(y, &5);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Value(7));
    /// ```
    #[inline]
    pub fn get_or_insert(this: &mut Self, value: T) -> &mut T {
        Almost::get_or_insert_with(this, || value)
    }

    /// Inserts the default value into the almost if it is [`Nil`], then
    /// returns a mutable reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x = Nil;
    ///
    /// {
    ///     let y: &mut u32 = Almost::get_or_insert_default(&mut x);
    ///     assert_eq!(y, &0);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Value(7));
    /// ```
    #[inline]
    pub fn get_or_insert_default(this: &mut Self) -> &mut T
    where
        T: Default,
    {
        Almost::get_or_insert_with(this, T::default)
    }

    /// Inserts a value computed from `f` into the almost if it is [`Nil`],
    /// then returns a mutable reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x = Nil;
    ///
    /// {
    ///     let y: &mut u32 = Almost::get_or_insert_with(&mut x, || 5);
    ///     assert_eq!(y, &5);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Value(7));
    /// ```
    #[inline]
    pub fn get_or_insert_with(this: &mut Self, f: impl FnOnce() -> T) -> &mut T {
        if let Nil = this {
            *this = Value(f());
        }

        // Safety: the code above just filled the option
        unsafe { Almost::unwrap_unchecked(Almost::as_mut(this)) }
    }

    /// Takes the value out of the almost, leaving a [`Nil`] in its place.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x = Value(2);
    /// let y = Almost::take(&mut x);
    /// assert_eq!(x, Nil);
    /// assert_eq!(y, Value(2));
    ///
    /// let mut x: Almost<u32> = Nil;
    /// let y = Almost::take(&mut x);
    /// assert_eq!(x, Nil);
    /// assert_eq!(y, Nil);
    /// ```
    #[inline]
    pub const fn take(this: &mut Self) -> Self {
        mem::replace(this, Nil)
    }

    /// Takes the value out of the almost, but only if the predicate evaluates to
    /// `true` on a mutable reference to the value.
    ///
    /// In other words, replaces `self` with `Nil` if the predicate returns `true`.
    /// This method operates similar to [`Almost::take`] but conditional.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x = Value(42);
    ///
    /// let prev = Almost::take_if(&mut x, |v| if *v == 42 {
    ///     *v += 1;
    ///     false
    /// } else {
    ///     false
    /// });
    /// assert_eq!(x, Value(43));
    /// assert_eq!(prev, Nil);
    ///
    /// let prev = Almost::take_if(&mut x, |v| *v == 43);
    /// assert_eq!(x, Nil);
    /// assert_eq!(prev, Value(43));
    /// ```
    #[inline]
    pub fn take_if(this: &mut Self, f: impl FnOnce(&mut T) -> bool) -> Self {
        if Almost::map_or(Almost::as_mut(this), false, f) {
            Almost::take(this)
        } else {
            Nil
        }
    }

    /// Replaces the actual value in the almost by the value given in parameter,
    /// returning the old value if present,
    /// leaving a [`Value`] in its place without deinitializing either one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let mut x = Value(2);
    /// let old = Almost::replace(&mut x, 5);
    /// assert_eq!(x, Value(5));
    /// assert_eq!(old, Value(2));
    ///
    /// let mut x = Nil;
    /// let old = Almost::replace(&mut x, 3);
    /// assert_eq!(x, Value(3));
    /// assert_eq!(old, Nil);
    /// ```
    #[inline]
    pub const fn replace(this: &mut Self, value: T) -> Self {
        mem::replace(this, Value(value))
    }

    /// Zips `self` with another `Almost`.
    ///
    /// If `self` is `Value(s)` and `other` is `Value(o)`, this method returns `Value((s, o))`.
    /// Otherwise, `Nil` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value(1);
    /// let y = Value("hi");
    /// let z = Nil::<u8>;
    ///
    /// assert_eq!(Almost::zip(x, y), Value((1, "hi")));
    /// assert_eq!(Almost::zip(x, z), Nil);
    /// ```
    #[inline]
    pub fn zip<U>(this: Self, other: Almost<U>) -> Almost<(T, U)> {
        match (this, other) {
            (Value(x), Value(y)) => Value((x, y)),
            _ => Nil,
        }
    }

    /// Zips `self` and another `Almost` with function `f`.
    ///
    /// If `self` is `Value(s)` and `other` is `Value(o)`, this method returns `Value(f(s, o))`.
    /// Otherwise, `Nil` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// #[derive(Debug, PartialEq)]
    /// struct Point {
    ///     x: f64,
    ///     y: f64,
    /// }
    ///
    /// impl Point {
    ///     fn new(x: f64, y: f64) -> Self {
    ///         Self { x, y }
    ///     }
    /// }
    ///
    /// let x = Value(17.5);
    /// let y = Value(42.7);
    ///
    /// assert_eq!(Almost::zip_with(x, y, Point::new), Value(Point { x: 17.5, y: 42.7 }));
    /// assert_eq!(Almost::zip_with(x, Nil, Point::new), Nil);
    /// ```
    #[inline]
    pub fn zip_with<U, R>(this: Self, other: Almost<U>, f: impl FnOnce(T, U) -> R) -> Almost<R> {
        match (this, other) {
            (Value(x), Value(y)) => Value(f(x, y)),
            _ => Nil,
        }
    }

    /// Return a reference the underlying value.
    ///
    /// # Panic
    ///
    /// Panics if `this` is `Nil`
    #[track_caller]
    pub const fn get_ref(this: &Self) -> &T {
        match this {
            Value(value) => value,
            Nil => panic!("Almost<T> was uninit"),
        }
    }

    /// Return a mutable reference the underlying value.
    ///
    /// # Panic
    ///
    /// Panics if `this` is `Nil`
    #[track_caller]
    pub const fn get_mut(this: &mut Self) -> &mut T {
        match this {
            Value(value) => value,
            Nil => panic!("Almost<T> was uninit"),
        }
    }

    /// Construct [`Almost<T>`] from [`Option<T>`].
    pub fn from_option(value: Option<T>) -> Self {
        match value {
            Some(x) => Value(x),
            None => Nil,
        }
    }
}

impl<T, U> Almost<(T, U)> {
    /// Unzips an almost containing a tuple of two almosts.
    ///
    /// If `self` is `Value((a, b))` this method returns `(Value(a), Value(b))`.
    /// Otherwise, `(Nil, Nil)` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = Value((1, "hi"));
    /// let y = Nil::<(u8, u32)>;
    ///
    /// assert_eq!(Almost::unzip(x), (Value(1), Value("hi")));
    /// assert_eq!(Almost::unzip(y), (Nil, Nil));
    /// ```
    #[inline]
    pub fn unzip(this: Self) -> (Almost<T>, Almost<U>) {
        match this {
            Value((x, y)) => (Value(x), Value(y)),
            Nil => (Nil, Nil),
        }
    }
}

impl<T> Almost<&'_ T> {
    /// Maps an `Almost<&T>` to an `Almost<T>` by copying the contents of the
    /// almost.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = 12;
    /// let opt_x = Value(&x);
    /// assert_eq!(opt_x, Value(&12));
    /// let copied = Almost::copied(opt_x);
    /// assert_eq!(copied, Value(12));
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub const fn copied(this: Self) -> Almost<T>
    where
        T: Copy,
    {
        match this {
            Value(&x) => Value(x),
            Nil => Nil,
        }
    }

    /// Maps an `Almost<&T>` to an `Almost<T>` by cloning the contents of the
    /// almost.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x = 12;
    /// let opt_x = Value(&x);
    /// assert_eq!(opt_x, Value(&12));
    /// let cloned = Almost::cloned(opt_x);
    /// assert_eq!(cloned, Value(12));
    /// ```
    pub fn cloned(this: Self) -> Almost<T>
    where
        T: Clone,
    {
        match this {
            Value(x) => Value(x.clone()),
            Nil => Nil,
        }
    }
}

impl<T, E> Almost<Result<T, E>> {
    /// Transposes an `Almost` of a [`Result`] into a [`Result`] of an `Almost`.
    ///
    /// [`Nil`] will be mapped to <code>[Ok]\([Nil])</code>.
    /// <code>[Value]\([Ok]\(\_))</code> and <code>[Value]\([Err]\(\_))</code> will be mapped to
    /// <code>[Ok]\([Value]\(\_))</code> and <code>[Err]\(\_)</code>.
    ///
    /// # Examples
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// #[derive(Debug, Eq, PartialEq)]
    /// struct SomeErr;
    ///
    /// let x: Result<Almost<i32>, SomeErr> = Ok(Value(5));
    /// let y: Almost<Result<i32, SomeErr>> = Value(Ok(5));
    /// assert_eq!(x, Almost::transpose(y));
    /// ```
    #[inline]
    pub fn transpose(this: Self) -> Result<Almost<T>, E> {
        match this {
            Value(Ok(x)) => Ok(Value(x)),
            Nil => Ok(Nil),
            Value(Err(e)) => Err(e),
        }
    }
}

impl<T> Almost<Almost<T>> {
    /// Converts from `Almost<Almost<T>>` to `Almost<T>`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<Almost<u32>> = Value(Value(6));
    /// assert_eq!(Value(6), Almost::flatten(x));
    ///
    /// let x: Almost<Almost<u32>> = Value(Nil);
    /// assert_eq!(Nil, Almost::flatten(x));
    ///
    /// let x: Almost<Almost<u32>> = Nil;
    /// assert_eq!(Nil, Almost::flatten(x));
    /// ```
    ///
    /// Flattening only removes one level of nesting at a time:
    ///
    /// ```
    /// # use for_sure::prelude::*;
    /// let x: Almost<Almost<Almost<u32>>> = Value(Value(Value(6)));
    /// assert_eq!(Value(Value(6)), Almost::flatten(x));
    /// assert_eq!(Value(6), Almost::flatten(Almost::flatten(x)));
    /// ```
    #[inline]
    pub fn flatten(this: Self) -> Almost<T> {
        match this {
            Value(Value(x)) => Value(x),
            Value(Nil) | Nil => Nil,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Almost<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Value(value) => fmt::Debug::fmt(&value, f),
            Nil => f.write_str("nil"),
        }
    }
}

impl<T> Deref for Almost<T> {
    type Target = T;

    /// Get a reference to the underlying data.
    ///
    /// # Panic
    ///
    /// Panics if self is `Nil`.
    #[track_caller]
    #[inline]
    fn deref(&self) -> &Self::Target {
        Self::get_ref(self)
    }
}

impl<T> DerefMut for Almost<T> {
    /// Get a mutable reference to the underlying data.
    ///
    /// # Panic
    ///
    /// Panics if self is `Nil`.
    #[track_caller]
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        Self::get_mut(self)
    }
}

impl<U: ?Sized, T: AsRef<U>> AsRef<U> for Almost<T> {
    #[inline]
    fn as_ref(&self) -> &U {
        Self::get_ref(self).as_ref()
    }
}

impl<'a, T> From<&'a Almost<T>> for Almost<&'a T> {
    #[inline]
    fn from(value: &'a Almost<T>) -> Self {
        Almost::as_ref(value)
    }
}

impl<'a, T> From<&'a mut Almost<T>> for Almost<&'a mut T> {
    #[inline]
    fn from(value: &'a mut Almost<T>) -> Self {
        Almost::as_mut(value)
    }
}

impl<T> From<T> for Almost<T> {
    #[inline]
    fn from(value: T) -> Self {
        Value(value)
    }
}

impl<T> From<Option<T>> for Almost<T> {
    #[inline]
    fn from(value: Option<T>) -> Self {
        match value {
            Some(x) => Value(x),
            None => Nil,
        }
    }
}

impl<T> From<Almost<T>> for Option<T> {
    #[inline]
    fn from(value: Almost<T>) -> Self {
        match value {
            Value(x) => Some(x),
            Nil => None,
        }
    }
}

impl<T: Clone> Clone for Almost<T> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Value(x) => Value(x.clone()),
            Nil => Nil,
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        match (self, source) {
            (Value(to), Value(from)) => to.clone_from(from),
            (to, from) => *to = from.clone(),
        }
    }
}

impl<T> IntoIterator for Almost<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            value: Almost::into_option(self),
        }
    }
}

impl<'a, T> IntoIterator for &'a Almost<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Almost::iter(self)
    }
}

impl<'a, T> IntoIterator for &'a mut Almost<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Almost::iter_mut(self)
    }
}

#[derive(Debug, Clone)]
pub struct IntoIter<T> {
    pub(crate) value: Option<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.value.take()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.value.take()
    }
}

impl<T> FusedIterator for IntoIter<T> {}

impl<T> ExactSizeIterator for IntoIter<T> {
    #[inline]
    fn len(&self) -> usize {
        match &self.value {
            Some(_) => 1,
            None => 0,
        }
    }
}

pub struct Iter<'a, T> {
    pub(crate) value: Option<&'a T>,
}

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Self {
            value: self.value,
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.value.take()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.value.take()
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

impl<T> ExactSizeIterator for Iter<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        match self.value {
            None => 0,
            Some(_) => 1,
        }
    }
}

pub struct IterMut<'a, T> {
    pub(crate) value: Option<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.value.take()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T> FusedIterator for IterMut<'_, T> {}

impl<T> ExactSizeIterator for IterMut<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        match self.value {
            Some(_) => 1,
            None => 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_as_ref() {
        let string = Value(String::from("a little string"));
        let s: &str = string.as_ref();
        assert_eq!(s, "a little string")
    }
}
