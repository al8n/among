//! Integration tests aimed at exercising branches that aren't already
//! covered by the inline `#[test]` functions and doctests in `src/`.

use among::{Among, IntoAmong, IterAmong, Left, Middle, Right};

// --- Construction / accessors / clone -------------------------------------

#[test]
fn clone_and_clone_from() {
  let a: Among<String, String, String> = Left("hello".to_string());
  let b = a.clone();
  assert_eq!(a, b);

  let m: Among<String, String, String> = Middle("middle".to_string());
  let n = m.clone();
  assert_eq!(m, n);

  let r: Among<String, String, String> = Right("right".to_string());
  let s = r.clone();
  assert_eq!(r, s);

  // clone_from same-variant fast paths
  let mut dst: Among<String, String, String> = Left("a".into());
  dst.clone_from(&Left("b".to_string()));
  assert_eq!(dst, Left("b".into()));

  let mut dst: Among<String, String, String> = Middle("a".into());
  dst.clone_from(&Middle("b".to_string()));
  assert_eq!(dst, Middle("b".into()));

  let mut dst: Among<String, String, String> = Right("a".into());
  dst.clone_from(&Right("b".to_string()));
  assert_eq!(dst, Right("b".into()));

  // Mismatched variant fallthrough
  let mut dst: Among<String, String, String> = Left("a".into());
  dst.clone_from(&Right("z".to_string()));
  assert_eq!(dst, Right("z".into()));
}

#[test]
fn pin_projections() {
  use core::pin::Pin;

  let pinned_l: Pin<&Among<i32, i32, i32>> = Pin::new(&Left(1));
  let _proj = pinned_l.as_pin_ref();

  let pinned_m: Pin<&Among<i32, i32, i32>> = Pin::new(&Middle(2));
  let _proj = pinned_m.as_pin_ref();

  let pinned_r: Pin<&Among<i32, i32, i32>> = Pin::new(&Right(3));
  let _proj = pinned_r.as_pin_ref();

  let mut l: Among<i32, i32, i32> = Left(1);
  let _ = Pin::new(&mut l).as_pin_mut();
  let mut m: Among<i32, i32, i32> = Middle(2);
  let _ = Pin::new(&mut m).as_pin_mut();
  let mut r: Among<i32, i32, i32> = Right(3);
  let _ = Pin::new(&mut r).as_pin_mut();
}

// --- unwrap_*/expect_* panic paths ----------------------------------------

#[test]
#[should_panic]
fn unwrap_left_on_middle() {
  let m: Among<(), i32, ()> = Middle(1);
  m.unwrap_left();
}
#[test]
#[should_panic]
fn unwrap_left_on_right() {
  let r: Among<(), (), i32> = Right(1);
  r.unwrap_left();
}
#[test]
#[should_panic]
fn unwrap_middle_on_left() {
  let l: Among<i32, (), ()> = Left(1);
  l.unwrap_middle();
}
#[test]
#[should_panic]
fn unwrap_middle_on_right() {
  let r: Among<(), (), i32> = Right(1);
  r.unwrap_middle();
}
#[test]
#[should_panic]
fn unwrap_right_on_left() {
  let l: Among<i32, (), ()> = Left(1);
  l.unwrap_right();
}
#[test]
#[should_panic]
fn unwrap_right_on_middle() {
  let m: Among<(), i32, ()> = Middle(1);
  m.unwrap_right();
}

#[test]
#[should_panic(expected = "msg-l")]
fn expect_left_on_middle() {
  let m: Among<(), i32, ()> = Middle(1);
  m.expect_left("msg-l");
}
#[test]
#[should_panic(expected = "msg-l")]
fn expect_left_on_right() {
  let r: Among<(), (), i32> = Right(1);
  r.expect_left("msg-l");
}
#[test]
#[should_panic(expected = "msg-m")]
fn expect_middle_on_left() {
  let l: Among<i32, (), ()> = Left(1);
  l.expect_middle("msg-m");
}
#[test]
#[should_panic(expected = "msg-m")]
fn expect_middle_on_right() {
  let r: Among<(), (), i32> = Right(1);
  r.expect_middle("msg-m");
}
#[test]
#[should_panic(expected = "msg-r")]
fn expect_right_on_left() {
  let l: Among<i32, (), ()> = Left(1);
  l.expect_right("msg-r");
}
#[test]
#[should_panic(expected = "msg-r")]
fn expect_right_on_middle() {
  let m: Among<(), i32, ()> = Middle(1);
  m.expect_right("msg-r");
}

// --- factor_* / map / inner / cloned ---------------------------------------

#[test]
fn factor_first_second_all_variants() {
  let l: Among<(u32, i32), (u32, &str), (u32, bool)> = Left((1, 2));
  let (t, rest) = l.factor_first();
  assert_eq!(t, 1);
  assert_eq!(rest, Left(2));

  let m: Among<(u32, i32), (u32, &str), (u32, bool)> = Middle((2, "x"));
  let (t, rest) = m.factor_first();
  assert_eq!(t, 2);
  assert_eq!(rest, Middle("x"));

  let r: Among<(u32, i32), (u32, &str), (u32, bool)> = Right((3, true));
  let (t, rest) = r.factor_first();
  assert_eq!(t, 3);
  assert_eq!(rest, Right(true));

  let l: Among<(i32, u32), (&str, u32), (bool, u32)> = Left((2, 1));
  let (rest, t) = l.factor_second();
  assert_eq!(t, 1);
  assert_eq!(rest, Left(2));

  let m: Among<(i32, u32), (&str, u32), (bool, u32)> = Middle(("x", 2));
  let (rest, t) = m.factor_second();
  assert_eq!(t, 2);
  assert_eq!(rest, Middle("x"));

  let r: Among<(i32, u32), (&str, u32), (bool, u32)> = Right((true, 3));
  let (rest, t) = r.factor_second();
  assert_eq!(t, 3);
  assert_eq!(rest, Right(true));
}

#[test]
fn factor_none_all_variants() {
  let l: Among<Option<i32>, Option<i32>, Option<i32>> = Left(Some(1));
  assert_eq!(l.factor_none(), Some(Left(1)));
  let l: Among<Option<i32>, Option<i32>, Option<i32>> = Left(None);
  assert_eq!(l.factor_none(), None);

  let m: Among<Option<i32>, Option<i32>, Option<i32>> = Middle(Some(2));
  assert_eq!(m.factor_none(), Some(Middle(2)));
  let m: Among<Option<i32>, Option<i32>, Option<i32>> = Middle(None);
  assert_eq!(m.factor_none(), None);

  let r: Among<Option<i32>, Option<i32>, Option<i32>> = Right(Some(3));
  assert_eq!(r.factor_none(), Some(Right(3)));
  let r: Among<Option<i32>, Option<i32>, Option<i32>> = Right(None);
  assert_eq!(r.factor_none(), None);
}

#[test]
fn factor_err_all_variants() {
  let l: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Left(Ok(1));
  assert_eq!(l.factor_err(), Ok(Left(1)));
  let l: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Left(Err("e"));
  assert_eq!(l.factor_err(), Err("e"));

  let m: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Middle(Ok(2));
  assert_eq!(m.factor_err(), Ok(Middle(2)));
  let m: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Middle(Err("e"));
  assert_eq!(m.factor_err(), Err("e"));

  let r: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Right(Ok(3));
  assert_eq!(r.factor_err(), Ok(Right(3)));
  let r: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Right(Err("e"));
  assert_eq!(r.factor_err(), Err("e"));
}

#[test]
fn factor_ok_all_variants() {
  let l: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Left(Ok(1));
  assert_eq!(l.factor_ok(), Ok(1));
  let l: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Left(Err("e"));
  assert_eq!(l.factor_ok(), Err(Left("e")));

  let m: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Middle(Ok(2));
  assert_eq!(m.factor_ok(), Ok(2));
  let m: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Middle(Err("e"));
  assert_eq!(m.factor_ok(), Err(Middle("e")));

  let r: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Right(Ok(3));
  assert_eq!(r.factor_ok(), Ok(3));
  let r: Among<Result<i32, &str>, Result<i32, &str>, Result<i32, &str>> = Right(Err("e"));
  assert_eq!(r.factor_ok(), Err(Right("e")));
}

#[test]
fn map_all_variants_for_ttt() {
  let l: Among<i32, i32, i32> = Left(2);
  assert_eq!(l.map(|x| x + 1), Left(3));
  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(m.map(|x| x + 1), Middle(3));
  let r: Among<i32, i32, i32> = Right(2);
  assert_eq!(r.map(|x| x + 1), Right(3));
}

#[test]
fn cloned_copied_ref_and_mut() {
  let val_l: Among<String, String, String> = Left("a".to_string());
  let r_l: Among<&String, &String, &String> = val_l.as_ref();
  assert_eq!(r_l.cloned(), Left("a".to_string()));

  let val_m: Among<String, String, String> = Middle("b".to_string());
  assert_eq!(val_m.as_ref().cloned(), Middle("b".to_string()));

  let val_r: Among<String, String, String> = Right("c".to_string());
  assert_eq!(val_r.as_ref().cloned(), Right("c".to_string()));

  let val_l: Among<i32, i32, i32> = Left(1);
  assert_eq!(val_l.as_ref().copied(), Left(1));
  let val_m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(val_m.as_ref().copied(), Middle(2));
  let val_r: Among<i32, i32, i32> = Right(3);
  assert_eq!(val_r.as_ref().copied(), Right(3));

  // mut ref versions
  let mut val_l: Among<String, String, String> = Left("a".to_string());
  let cloned = val_l.as_mut().cloned();
  assert_eq!(cloned, Left("a".to_string()));
  let mut val_m: Among<String, String, String> = Middle("b".to_string());
  let cloned = val_m.as_mut().cloned();
  assert_eq!(cloned, Middle("b".to_string()));
  let mut val_r: Among<String, String, String> = Right("c".to_string());
  let cloned = val_r.as_mut().cloned();
  assert_eq!(cloned, Right("c".to_string()));

  let mut val_l: Among<i32, i32, i32> = Left(1);
  assert_eq!(val_l.as_mut().copied(), Left(1));
  let mut val_m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(val_m.as_mut().copied(), Middle(2));
  let mut val_r: Among<i32, i32, i32> = Right(3);
  assert_eq!(val_r.as_mut().copied(), Right(3));
}

// --- insert/get_or_insert -------------------------------------------------

#[test]
fn insert_methods() {
  let mut a: Among<u32, u32, u32> = Right(1);
  *a.insert_left(10) += 1;
  assert_eq!(a, Left(11));

  let mut a: Among<u32, u32, u32> = Left(1);
  *a.insert_middle(20) += 1;
  assert_eq!(a, Middle(21));

  let mut a: Among<u32, u32, u32> = Left(1);
  *a.insert_right(30) += 1;
  assert_eq!(a, Right(31));
}

#[test]
fn get_or_insert_methods() {
  let mut a: Among<u32, u32, u32> = Right(1);
  let l = a.get_or_insert_left(7);
  assert_eq!(*l, 7);
  assert_eq!(a, Left(7));

  let mut a: Among<u32, u32, u32> = Left(5);
  assert_eq!(*a.get_or_insert_left(99), 5);

  let mut a: Among<u32, u32, u32> = Right(1);
  let m = a.get_or_insert_middle(8);
  assert_eq!(*m, 8);
  assert_eq!(a, Middle(8));

  let mut a: Among<u32, u32, u32> = Middle(5);
  assert_eq!(*a.get_or_insert_middle(99), 5);

  let mut a: Among<u32, u32, u32> = Left(1);
  let r = a.get_or_insert_right(9);
  assert_eq!(*r, 9);
  assert_eq!(a, Right(9));

  let mut a: Among<u32, u32, u32> = Right(5);
  assert_eq!(*a.get_or_insert_right(99), 5);

  // _with variants
  let mut a: Among<u32, u32, u32> = Right(1);
  let l = a.get_or_insert_left_with(|| 42);
  *l += 1;
  assert_eq!(a, Left(43));

  let mut a: Among<u32, u32, u32> = Right(1);
  let m = a.get_or_insert_middle_with(|| 42);
  *m += 1;
  assert_eq!(a, Middle(43));

  let mut a: Among<u32, u32, u32> = Left(1);
  let r = a.get_or_insert_right_with(|| 42);
  *r += 1;
  assert_eq!(a, Right(43));
}

#[test]
fn try_among_into_branches() {
  let l: Among<i64, i32, u32> = Left(3i64);
  assert_eq!(l.try_among_into::<i32>().ok(), Some(3));
  let l: Among<i64, i32, u32> = Left(i64::MAX);
  assert!(matches!(l.try_among_into::<i32>(), Err(Left(_))));

  let m: Among<i64, i32, u32> = Middle(3);
  assert_eq!(m.try_among_into::<i32>().ok(), Some(3));

  let r: Among<i64, i32, u32> = Right(3u32);
  assert_eq!(r.try_among_into::<i32>().ok(), Some(3));
  let r: Among<i64, i32, u32> = Right(u32::MAX);
  assert!(matches!(r.try_among_into::<i32>(), Err(Right(_))));
}

#[test]
fn into_inner_as_inner() {
  let l: Among<i32, i32, i32> = Left(1);
  assert_eq!(l.into_inner(), 1);
  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(m.into_inner(), 2);
  let r: Among<i32, i32, i32> = Right(3);
  assert_eq!(r.into_inner(), 3);

  let l: Among<i32, i32, i32> = Left(1);
  assert_eq!(*l.as_inner(), 1);
  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(*m.as_inner(), 2);
  let r: Among<i32, i32, i32> = Right(3);
  assert_eq!(*r.as_inner(), 3);

  let mut l: Among<i32, i32, i32> = Left(1);
  *l.as_inner_mut() = 11;
  assert_eq!(l, Left(11));
  let mut m: Among<i32, i32, i32> = Middle(2);
  *m.as_inner_mut() = 22;
  assert_eq!(m, Middle(22));
  let mut r: Among<i32, i32, i32> = Right(3);
  *r.as_inner_mut() = 33;
  assert_eq!(r, Right(33));
}

#[test]
fn among_into() {
  let l: Among<u16, u32, u64> = Left(3u16);
  assert_eq!(l.among_into::<u64>(), 3);
  let m: Among<u16, u32, u64> = Middle(3u32);
  assert_eq!(m.among_into::<u64>(), 3);
  let r: Among<u16, u32, u64> = Right(3u64);
  assert_eq!(r.among_into::<u64>(), 3);
}

#[test]
fn flip_and_shift_all_variants() {
  let l: Among<i32, i32, i32> = Left(1);
  assert_eq!(l.flip(), Right(1));
  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(m.flip(), Middle(2));
  let r: Among<i32, i32, i32> = Right(3);
  assert_eq!(r.flip(), Left(3));

  assert_eq!(Left::<i32, i32, i32>(1).flip_left_middle(), Middle(1));
  assert_eq!(Middle::<i32, i32, i32>(2).flip_left_middle(), Left(2));
  assert_eq!(Right::<i32, i32, i32>(3).flip_left_middle(), Right(3));

  assert_eq!(Left::<i32, i32, i32>(1).flip_middle_right(), Left(1));
  assert_eq!(Middle::<i32, i32, i32>(2).flip_middle_right(), Right(2));
  assert_eq!(Right::<i32, i32, i32>(3).flip_middle_right(), Middle(3));

  assert_eq!(Left::<i32, i32, i32>(1).shift_right(), Middle(1));
  assert_eq!(Middle::<i32, i32, i32>(2).shift_right(), Right(2));
  assert_eq!(Right::<i32, i32, i32>(3).shift_right(), Left(3));

  assert_eq!(Left::<i32, i32, i32>(1).shift_left(), Right(1));
  assert_eq!(Middle::<i32, i32, i32>(2).shift_left(), Left(2));
  assert_eq!(Right::<i32, i32, i32>(3).shift_left(), Middle(3));
}

#[test]
fn map_left_middle_right_all() {
  // Cover branches not directly cited by doctests (Left passing through map_middle/right etc.).
  let l: Among<i32, i32, i32> = Left(1);
  assert_eq!(l.map_middle(|x| x + 100), Left(1));
  let r: Among<i32, i32, i32> = Right(3);
  assert_eq!(r.map_middle(|x| x + 100), Right(3));

  let l: Among<i32, i32, i32> = Left(1);
  assert_eq!(l.map_right(|x| x + 100), Left(1));
  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(m.map_right(|x| x + 100), Middle(2));

  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(m.map_left(|x| x + 100), Middle(2));
  let r: Among<i32, i32, i32> = Right(3);
  assert_eq!(r.map_left(|x| x + 100), Right(3));

  // map_among on Middle (not in doctests)
  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(m.map_among(|x| x + 1, |x| x + 2, |x| x + 3), Middle(4));

  // map_among_with on Middle
  let mut sum = 0i32;
  let m: Among<i32, i32, i32> = Middle(2);
  let _ = m.map_among_with(
    &mut sum,
    |s, x| {
      *s += x;
      x
    },
    |s, x| {
      *s += x;
      x
    },
    |s, x| {
      *s += x;
      x
    },
  );
  assert_eq!(sum, 2);
}

#[test]
fn left_and_then_others_pass_through() {
  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(
    m.left_and_then(|x| Among::<i32, i32, i32>::Right(x * 2)),
    Middle(2)
  );
  // middle_and_then passing Left through
  let l: Among<i32, i32, i32> = Left(1);
  assert_eq!(
    l.middle_and_then(|x| Among::<i32, i32, i32>::Right(x * 2)),
    Left(1)
  );
  // right_and_then passing Middle through
  let m: Among<i32, i32, i32> = Middle(2);
  assert_eq!(m.right_and_then(|x| Right(x * 2)), Middle(2));
}

#[test]
fn or_default_and_or_else_branches() {
  let r: Among<String, i32, i32> = Right(0);
  assert_eq!(r.left_or_default(), String::default());
  let l: Among<String, i32, i32> = Left("a".to_string());
  assert_eq!(l.left_or_default(), "a".to_string());

  let l: Among<i32, String, i32> = Left(0);
  assert_eq!(l.middle_or_default(), String::default());

  let m: Among<i32, i32, String> = Middle(0);
  assert_eq!(m.right_or_default(), String::default());

  let r: Among<i32, i32, String> = Right("r".to_string());
  assert_eq!(r.right_or_default(), "r".to_string());

  let r: Among<i32, i32, String> = Right("r".to_string());
  assert_eq!(r.right_or("x".to_string()), "r".to_string());
}

#[test]
fn inspect_methods_no_call() {
  // Ensure non-matching variants don't call the closure.
  let m: Among<i32, i32, i32> = Middle(2);
  let _ = m.inspect_left(|_| panic!("not called"));
  let l: Among<i32, i32, i32> = Left(1);
  let _ = l.inspect_middle(|_| panic!("not called"));
  let m: Among<i32, i32, i32> = Middle(2);
  let _ = m.inspect_right(|_| panic!("not called"));
}

// --- Display, Debug, Hash, Ord -------------------------------------------

#[test]
fn display_impl() {
  use std::string::ToString;
  let l: Among<i32, &str, bool> = Left(1);
  assert_eq!(l.to_string(), "1");
  let m: Among<i32, &str, bool> = Middle("hi");
  assert_eq!(m.to_string(), "hi");
  let r: Among<i32, &str, bool> = Right(true);
  assert_eq!(r.to_string(), "true");
}

#[cfg(feature = "std")]
#[test]
fn error_impl() {
  use std::{error::Error as _, fmt, io};

  #[derive(Debug)]
  struct E;
  impl fmt::Display for E {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      f.write_str("E")
    }
  }
  impl std::error::Error for E {}

  let err = io::Error::other("boom");
  let a: Among<E, io::Error, E> = Middle(err);
  let _ = a.source();

  #[allow(deprecated)]
  let _ = a.description();
  #[allow(deprecated)]
  let _ = a.cause();

  let a: Among<E, io::Error, E> = Left(E);
  let _ = a.source();
  #[allow(deprecated)]
  let _ = a.description();
  #[allow(deprecated)]
  let _ = a.cause();

  let a: Among<E, io::Error, E> = Right(E);
  let _ = a.source();
  #[allow(deprecated)]
  let _ = a.description();
  #[allow(deprecated)]
  let _ = a.cause();
}

#[test]
fn as_ref_and_as_mut_target_impls() {
  fn slice_of<T: AsRef<[i32]>>(t: &T) -> &[i32] {
    t.as_ref()
  }
  fn slice_mut_of<T: AsMut<[i32]>>(t: &mut T) -> &mut [i32] {
    t.as_mut()
  }
  fn str_of<T: AsRef<str>>(t: &T) -> &str {
    t.as_ref()
  }
  fn str_mut_of<T: AsMut<str>>(t: &mut T) -> &mut str {
    t.as_mut()
  }
  fn vec_ref<T: AsRef<Vec<u8>>>(t: &T) -> &Vec<u8> {
    t.as_ref()
  }
  fn vec_mut<T: AsMut<Vec<u8>>>(t: &mut T) -> &mut Vec<u8> {
    t.as_mut()
  }

  // [Target] AsRef on each variant
  let l: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Left(vec![1, 2, 3]);
  assert_eq!(slice_of(&l), &[1, 2, 3]);
  let m: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Middle(vec![4, 5]);
  assert_eq!(slice_of(&m), &[4, 5]);
  let r: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Right(vec![6]);
  assert_eq!(slice_of(&r), &[6]);

  // [Target] AsMut on each variant
  let mut l: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Left(vec![1]);
  slice_mut_of(&mut l)[0] = 9;
  assert_eq!(l, Left(vec![9]));
  let mut m: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Middle(vec![1]);
  slice_mut_of(&mut m)[0] = 9;
  let mut r: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Right(vec![1]);
  slice_mut_of(&mut r)[0] = 9;

  // str AsRef/AsMut on each variant
  let l: Among<String, String, String> = Left("a".to_string());
  assert_eq!(str_of(&l), "a");
  let m: Among<String, String, String> = Middle("a".to_string());
  assert_eq!(str_of(&m), "a");
  let r: Among<String, String, String> = Right("a".to_string());
  assert_eq!(str_of(&r), "a");

  let mut l: Among<String, String, String> = Left("a".to_string());
  str_mut_of(&mut l).make_ascii_uppercase();
  assert_eq!(l, Left("A".to_string()));
  let mut m: Among<String, String, String> = Middle("a".to_string());
  str_mut_of(&mut m).make_ascii_uppercase();
  let mut r: Among<String, String, String> = Right("a".to_string());
  str_mut_of(&mut r).make_ascii_uppercase();

  // generic Target AsMut on each variant
  let mut l: Among<Vec<u8>, Vec<u8>, Vec<u8>> = Left(vec![1u8]);
  vec_mut(&mut l).push(2);
  assert_eq!(l, Left(vec![1, 2]));
  let mut m: Among<Vec<u8>, Vec<u8>, Vec<u8>> = Middle(vec![1u8]);
  vec_mut(&mut m).push(2);
  let mut r: Among<Vec<u8>, Vec<u8>, Vec<u8>> = Right(vec![1u8]);
  vec_mut(&mut r).push(2);

  // generic Target AsRef on each variant
  let l: Among<Vec<u8>, Vec<u8>, Vec<u8>> = Left(vec![1]);
  assert_eq!(vec_ref(&l), &vec![1u8]);
  let m: Among<Vec<u8>, Vec<u8>, Vec<u8>> = Middle(vec![1]);
  assert_eq!(vec_ref(&m), &vec![1u8]);
  let r: Among<Vec<u8>, Vec<u8>, Vec<u8>> = Right(vec![1]);
  assert_eq!(vec_ref(&r), &vec![1u8]);
}

#[cfg(feature = "std")]
#[test]
fn as_ref_path_osstr_cstr_impls() {
  use std::{
    ffi::{CStr, CString, OsStr, OsString},
    path::{Path, PathBuf},
  };

  fn path_of<T: AsRef<Path>>(t: &T) -> &Path {
    t.as_ref()
  }
  fn osstr_of<T: AsRef<OsStr>>(t: &T) -> &OsStr {
    t.as_ref()
  }
  fn cstr_of<T: AsRef<CStr>>(t: &T) -> &CStr {
    t.as_ref()
  }

  for v in [
    Left::<PathBuf, PathBuf, PathBuf>(PathBuf::from("/tmp")),
    Middle(PathBuf::from("/tmp")),
    Right(PathBuf::from("/tmp")),
  ] {
    assert_eq!(path_of(&v), Path::new("/tmp"));
  }

  for v in [
    Left::<OsString, OsString, OsString>(OsString::from("x")),
    Middle(OsString::from("x")),
    Right(OsString::from("x")),
  ] {
    assert_eq!(osstr_of(&v), OsStr::new("x"));
  }

  for v in [
    Left::<CString, CString, CString>(CString::new("hello").unwrap()),
    Middle(CString::new("hello").unwrap()),
    Right(CString::new("hello").unwrap()),
  ] {
    assert_eq!(cstr_of(&v).to_bytes(), b"hello");
  }
}

#[test]
fn deref_mut_works() {
  use std::string::String;
  let mut a: Among<String, String, String> = Left("hi".to_string());
  let r: &mut str = &mut *a;
  r.make_ascii_uppercase();
  assert_eq!(a, Left("HI".to_string()));

  let mut a: Among<String, String, String> = Middle("hi".to_string());
  let r: &mut str = &mut *a;
  r.make_ascii_uppercase();
  assert_eq!(a, Middle("HI".to_string()));

  let mut a: Among<String, String, String> = Right("hi".to_string());
  let r: &mut str = &mut *a;
  r.make_ascii_uppercase();
  assert_eq!(a, Right("HI".to_string()));
}

#[cfg(feature = "std")]
#[test]
fn bufread_impl() {
  use std::io::{BufRead, Cursor};

  fn run<T: BufRead>(mut r: T) {
    let mut s = String::new();
    let _ = r.read_line(&mut s).unwrap();
    let mut v = Vec::new();
    let _ = r.read_until(b'\n', &mut v).unwrap();
    let _ = r.fill_buf().unwrap();
    r.consume(0);
  }

  let l: Among<Cursor<&[u8]>, Cursor<&[u8]>, Cursor<&[u8]>> = Left(Cursor::new(b"hello\nworld\n"));
  run(l);
  let m: Among<Cursor<&[u8]>, Cursor<&[u8]>, Cursor<&[u8]>> = Middle(Cursor::new(b"hi\nthere\n"));
  run(m);
  let r: Among<Cursor<&[u8]>, Cursor<&[u8]>, Cursor<&[u8]>> = Right(Cursor::new(b"a\nb\n"));
  run(r);
}

#[cfg(feature = "std")]
#[test]
fn write_and_read_extras() {
  use std::io::{Read, Seek, SeekFrom, Write};

  // Read variants: read_exact, read_to_end, read_to_string
  let data = b"abc";
  let mut a: Among<&[u8], &[u8], &[u8]> = Middle(&data[..]);
  let mut buf = [0u8; 3];
  a.read_exact(&mut buf).unwrap();
  assert_eq!(&buf, b"abc");

  let mut a: Among<&[u8], &[u8], &[u8]> = Left(&data[..]);
  let mut v = Vec::new();
  a.read_to_end(&mut v).unwrap();
  assert_eq!(v, b"abc");

  let mut a: Among<&[u8], &[u8], &[u8]> = Right(&data[..]);
  let mut s = String::new();
  a.read_to_string(&mut s).unwrap();
  assert_eq!(s, "abc");

  // Seek for Middle and Left variants
  let mut buf = std::io::Cursor::new(vec![0u8; 4]);
  let mut a: Among<std::io::Cursor<Vec<u8>>, std::io::Cursor<Vec<u8>>, std::io::Cursor<Vec<u8>>> =
    Middle(buf.clone());
  a.seek(SeekFrom::Start(2)).unwrap();
  let _ = buf.write_all(b"xx");
  let mut a: Among<std::io::Cursor<Vec<u8>>, std::io::Cursor<Vec<u8>>, std::io::Cursor<Vec<u8>>> =
    Left(buf.clone());
  a.seek(SeekFrom::Start(0)).unwrap();

  // Write methods on all variants
  let mut buf = Vec::<u8>::new();
  let mut w: Among<&mut Vec<u8>, &mut Vec<u8>, &mut Vec<u8>> = Middle(&mut buf);
  w.write_all(b"x").unwrap();
  w.flush().unwrap();
  let _ = w.write_fmt(format_args!("{}", 42));

  let mut buf = Vec::<u8>::new();
  let mut w: Among<&mut Vec<u8>, &mut Vec<u8>, &mut Vec<u8>> = Left(&mut buf);
  w.write_all(b"a").unwrap();
  w.flush().unwrap();
  let _ = w.write_fmt(format_args!("{}", 1));

  let mut buf = Vec::<u8>::new();
  let mut w: Among<&mut Vec<u8>, &mut Vec<u8>, &mut Vec<u8>> = Right(&mut buf);
  w.write_all(b"r").unwrap();
  w.flush().unwrap();
  let _ = w.write_fmt(format_args!("{}", 2));
}

// --- IntoAmong ------------------------------------------------------------

#[test]
fn into_among_branches() {
  assert_eq!(5u8.into_among(Some(true)), Left(5));
  assert_eq!(5u8.into_among(Some(false)), Right(5));
  assert_eq!(5u8.into_among(None), Middle(5));

  fn classify(x: &i32) -> Option<bool> {
    if *x > 0 {
      Some(true)
    } else if *x == 0 {
      None
    } else {
      Some(false)
    }
  }
  assert_eq!(1.into_among_with(classify), Left(1));
  assert_eq!(0.into_among_with(classify), Middle(0));
  assert_eq!((-1).into_among_with(classify), Right(-1));
}

// --- Iterator / DoubleEndedIterator / ExactSize / IterAmong ---------------

#[test]
fn among_iterator_methods() {
  // Use Vec<u8> for L/M/R so they share the same Item.
  type A = Among<std::vec::IntoIter<i32>, std::vec::IntoIter<i32>, std::vec::IntoIter<i32>>;

  fn from_left(v: Vec<i32>) -> A {
    Left(v.into_iter())
  }
  fn from_middle(v: Vec<i32>) -> A {
    Middle(v.into_iter())
  }
  fn from_right(v: Vec<i32>) -> A {
    Right(v.into_iter())
  }

  // size_hint, fold, for_each, count, last, nth, collect, partition, all, any,
  // find, find_map, position
  for builder in [
    from_left as fn(Vec<i32>) -> A,
    from_middle as fn(Vec<i32>) -> A,
    from_right as fn(Vec<i32>) -> A,
  ] {
    let it = builder(vec![1, 2, 3, 4]);
    assert_eq!(it.size_hint().0, 4);
    let it = builder(vec![1, 2, 3, 4]);
    assert_eq!(it.fold(0, |a, x| a + x), 10);
    let mut total = 0;
    builder(vec![1, 2, 3, 4]).for_each(|x| total += x);
    assert_eq!(total, 10);
    assert_eq!(builder(vec![1, 2, 3, 4]).count(), 4);
    assert_eq!(builder(vec![1, 2, 3, 4]).last(), Some(4));
    assert_eq!(builder(vec![1, 2, 3, 4]).nth(2), Some(3));
    let v: Vec<i32> = builder(vec![1, 2, 3, 4]).collect();
    assert_eq!(v, vec![1, 2, 3, 4]);
    let (evens, odds): (Vec<_>, Vec<_>) = builder(vec![1, 2, 3, 4]).partition(|x| x % 2 == 0);
    assert_eq!(evens, vec![2, 4]);
    assert_eq!(odds, vec![1, 3]);
    let mut it = builder(vec![1, 2, 3]);
    assert!(it.all(|x| x > 0));
    let mut it = builder(vec![1, 2, 3]);
    assert!(it.any(|x| x == 2));
    let mut it = builder(vec![1, 2, 3]);
    assert_eq!(it.find(|x| *x == 2), Some(2));
    let mut it = builder(vec![1, 2, 3]);
    assert_eq!(
      it.find_map(|x| if x == 2 { Some(x * 10) } else { None }),
      Some(20)
    );
    let mut it = builder(vec![1, 2, 3]);
    assert_eq!(it.position(|x| x == 3), Some(2));
  }
}

#[test]
fn among_double_ended_and_exact_size() {
  type A = Among<std::vec::IntoIter<i32>, std::vec::IntoIter<i32>, std::vec::IntoIter<i32>>;
  fn make(v: Vec<i32>, kind: u8) -> A {
    match kind {
      0 => Left(v.into_iter()),
      1 => Middle(v.into_iter()),
      _ => Right(v.into_iter()),
    }
  }

  for k in 0..3 {
    let mut it = make(vec![1, 2, 3], k);
    assert_eq!(it.next_back(), Some(3));
    let mut it = make(vec![1, 2, 3], k);
    assert_eq!(it.nth_back(1), Some(2));
    let it = make(vec![1, 2, 3], k);
    assert_eq!(it.rfold(0, |acc, x| acc + x), 6);
    let mut it = make(vec![1, 2, 3], k);
    assert_eq!(it.rfind(|x| *x == 1), Some(1));
    let it = make(vec![1, 2, 3], k);
    assert_eq!(it.len(), 3);
  }
}

#[test]
fn iter_among_iterator_methods() {
  // Build IterAmong with three different IntoIter types.
  fn left() -> IterAmong<std::vec::IntoIter<i32>, std::vec::IntoIter<i32>, std::vec::IntoIter<i32>>
  {
    Among::<Vec<i32>, Vec<i32>, Vec<i32>>::Left(vec![1, 2, 3]).factor_into_iter()
  }
  fn middle() -> IterAmong<std::vec::IntoIter<i32>, std::vec::IntoIter<i32>, std::vec::IntoIter<i32>>
  {
    Among::<Vec<i32>, Vec<i32>, Vec<i32>>::Middle(vec![4, 5, 6]).factor_into_iter()
  }
  fn right() -> IterAmong<std::vec::IntoIter<i32>, std::vec::IntoIter<i32>, std::vec::IntoIter<i32>>
  {
    Among::<Vec<i32>, Vec<i32>, Vec<i32>>::Right(vec![7, 8, 9]).factor_into_iter()
  }

  type Builder =
    fn() -> IterAmong<std::vec::IntoIter<i32>, std::vec::IntoIter<i32>, std::vec::IntoIter<i32>>;
  let builders: [Builder; 3] = [left, middle, right];
  for builder in builders {
    let it = builder();
    let _ = it.size_hint();
    let it = builder();
    let _ = it.fold(0i32, |acc, x| match x {
      Left(l) => acc + l,
      Middle(m) => acc + m,
      Right(r) => acc + r,
    });
    let mut total = 0;
    builder().for_each(|x| match x {
      Left(l) => total += l,
      Middle(m) => total += m,
      Right(r) => total += r,
    });
    assert_eq!(builder().count(), 3);
    assert!(builder().last().is_some());
    let mut it = builder();
    assert!(it.nth(1).is_some());
    let v: Vec<_> = builder().collect();
    assert_eq!(v.len(), 3);
    let (a, b): (Vec<_>, Vec<_>) = builder().partition(|x| match x {
      Left(l) => *l > 1,
      Middle(m) => *m > 4,
      Right(r) => *r > 7,
    });
    assert!(!a.is_empty());
    assert!(!b.is_empty());

    let mut it = builder();
    let _ = it.all(|_| true);
    let mut it = builder();
    let _ = it.any(|_| true);
    let mut it = builder();
    let _ = it.find(|_| true);
    let mut it = builder();
    let _ = it.find_map(|x| match x {
      Left(l) => Some(l),
      Middle(m) => Some(m),
      Right(r) => Some(r),
    });
    let mut it = builder();
    let _ = it.position(|_| true);
  }
}

#[test]
fn iter_among_double_ended_and_exact() {
  for kind in 0..3u8 {
    let a: Among<Vec<i32>, Vec<i32>, Vec<i32>> = match kind {
      0 => Left(vec![1, 2, 3]),
      1 => Middle(vec![1, 2, 3]),
      _ => Right(vec![1, 2, 3]),
    };
    let mut it = a.factor_into_iter();
    let _ = it.next_back();
    let _ = it.nth_back(0);

    let a: Among<Vec<i32>, Vec<i32>, Vec<i32>> = match kind {
      0 => Left(vec![1, 2, 3]),
      1 => Middle(vec![1, 2, 3]),
      _ => Right(vec![1, 2, 3]),
    };
    let it = a.factor_into_iter();
    let _ = it.rfold(0, |acc, _| acc + 1);

    let a: Among<Vec<i32>, Vec<i32>, Vec<i32>> = match kind {
      0 => Left(vec![1, 2, 3]),
      1 => Middle(vec![1, 2, 3]),
      _ => Right(vec![1, 2, 3]),
    };
    let mut it = a.factor_into_iter();
    let _ = it.rfind(|_| true);

    let a: Among<Vec<i32>, Vec<i32>, Vec<i32>> = match kind {
      0 => Left(vec![1, 2, 3]),
      1 => Middle(vec![1, 2, 3]),
      _ => Right(vec![1, 2, 3]),
    };
    let it = a.factor_into_iter();
    assert_eq!(it.len(), 3);
  }
}

#[test]
fn iter_methods_factor_iter_iter_mut_etc() {
  let mut value: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Middle(vec![10, 20]);
  let collected: Vec<&i32> = value.iter().collect();
  assert_eq!(collected, vec![&10, &20]);
  for v in value.iter_mut() {
    *v += 1;
  }
  assert_eq!(value, Middle(vec![11, 21]));

  // factor_iter and factor_iter_mut for Middle
  let value: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Middle(vec![1, 2]);
  let v: Vec<_> = value.factor_iter().collect();
  assert_eq!(v.len(), 2);

  let mut value: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Middle(vec![1, 2]);
  for x in value.factor_iter_mut() {
    if let Middle(m) = x {
      *m += 100;
    }
  }
  assert_eq!(value, Middle(vec![101, 102]));
}

#[test]
fn extend_impl() {
  let mut a: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Left(vec![]);
  a.extend([1, 2, 3]);
  assert_eq!(a, Left(vec![1, 2, 3]));

  let mut a: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Middle(vec![]);
  a.extend([1, 2]);
  assert_eq!(a, Middle(vec![1, 2]));

  let mut a: Among<Vec<i32>, Vec<i32>, Vec<i32>> = Right(vec![]);
  a.extend([4]);
  assert_eq!(a, Right(vec![4]));
}

// --- Future impl ----------------------------------------------------------

#[test]
fn future_impl_polls_each_variant() {
  use core::{
    future::Future,
    pin::Pin,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
  };

  fn noop_waker() -> Waker {
    fn clone(_: *const ()) -> RawWaker {
      RawWaker::new(core::ptr::null(), &VTABLE)
    }
    fn noop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
  }

  use core::future::ready;

  // Each variant has its own Future type with the same Output = i32.
  let waker = noop_waker();
  let mut cx = Context::from_waker(&waker);

  let mut fut: Among<core::future::Ready<i32>, core::future::Ready<i32>, core::future::Ready<i32>> =
    Left(ready(1i32));
  let pinned = unsafe { Pin::new_unchecked(&mut fut) };
  match pinned.poll(&mut cx) {
    Poll::Ready(v) => assert_eq!(v, Left(1)),
    Poll::Pending => panic!(),
  }

  let mut fut: Among<core::future::Ready<i32>, _, core::future::Ready<i32>> = Middle(ready(2i32));
  let pinned = unsafe { Pin::new_unchecked(&mut fut) };
  match pinned.poll(&mut cx) {
    Poll::Ready(v) => assert_eq!(v, Middle(2)),
    Poll::Pending => panic!(),
  }

  let mut fut: Among<core::future::Ready<i32>, core::future::Ready<i32>, _> = Right(ready(3i32));
  let pinned = unsafe { Pin::new_unchecked(&mut fut) };
  match pinned.poll(&mut cx) {
    Poll::Ready(v) => assert_eq!(v, Right(3)),
    Poll::Pending => panic!(),
  }
}

// --- result_ext -----------------------------------------------------------

#[test]
fn among_ok_ext_branches() {
  use among::AmongOkExt;
  let r: Result<Among<i32, i32, i32>, ()> = Ok(Left(1));
  let r = r.map_left(|x| x + 1);
  assert_eq!(r, Ok(Left(2)));

  let r: Result<Among<i32, i32, i32>, ()> = Ok(Middle(2));
  let r = r.map_middle(|x| x + 1);
  assert_eq!(r, Ok(Middle(3)));

  let r: Result<Among<i32, i32, i32>, ()> = Ok(Right(3));
  let r = r.map_right(|x| x + 1);
  assert_eq!(r, Ok(Right(4)));
}

#[test]
fn among_err_ext_branches() {
  use among::AmongErrorExt;
  let r: Result<(), Among<i32, i32, i32>> = Err(Left(1));
  let r = r.map_err_left(|x| x + 1);
  assert_eq!(r, Err(Left(2)));

  let r: Result<(), Among<i32, i32, i32>> = Err(Middle(2));
  let r = r.map_err_middle(|x| x + 1);
  assert_eq!(r, Err(Middle(3)));

  let r: Result<(), Among<i32, i32, i32>> = Err(Right(3));
  let r = r.map_err_right(|x| x + 1);
  assert_eq!(r, Err(Right(4)));
}

// --- either feature -------------------------------------------------------

#[cfg(feature = "either")]
mod either_feature {
  use super::*;
  use either::Either;

  #[test]
  fn try_into_left_middle_right_variant() {
    let a: Among<i32, i32, i32> = Right(7);
    assert_eq!(a.try_into_left_middle(), Err(7));
  }
  #[test]
  fn try_into_middle_right_left_variant() {
    let a: Among<i32, i32, i32> = Left(7);
    assert_eq!(a.try_into_middle_right(), Err(7));
  }
  #[test]
  fn try_into_left_right_middle_variant() {
    let a: Among<i32, i32, i32> = Middle(7);
    assert_eq!(a.try_into_left_right(), Err(7));
  }

  #[test]
  #[should_panic]
  fn into_left_middle_panics_on_right() {
    let a: Among<i32, i32, i32> = Right(7);
    let _: Either<i32, i32> = a.into_left_middle();
  }
  #[test]
  #[should_panic]
  fn into_middle_right_panics_on_left() {
    let a: Among<i32, i32, i32> = Left(7);
    let _: Either<i32, i32> = a.into_middle_right();
  }
  #[test]
  #[should_panic]
  fn into_left_right_panics_on_middle() {
    let a: Among<i32, i32, i32> = Middle(7);
    let _: Either<i32, i32> = a.into_left_right();
  }

  #[test]
  fn from_either_variants() {
    let a: Among<i32, (), i32> = Among::from_either_to_left_right(Either::Right(2));
    assert_eq!(a, Right(2));

    let nested: Either<Either<i32, &str>, bool> = Either::Left(Either::Left(1));
    let a: Among<i32, &str, bool> = nested.into();
    assert_eq!(a, Left(1));
    let nested: Either<Either<i32, &str>, bool> = Either::Left(Either::Right("x"));
    let a: Among<i32, &str, bool> = nested.into();
    assert_eq!(a, Middle("x"));
    let nested: Either<Either<i32, &str>, bool> = Either::Right(true);
    let a: Among<i32, &str, bool> = nested.into();
    assert_eq!(a, Right(true));

    let nested: Either<i32, Either<&str, bool>> = Either::Left(1);
    let a: Among<i32, &str, bool> = nested.into();
    assert_eq!(a, Left(1));
    let nested: Either<i32, Either<&str, bool>> = Either::Right(Either::Left("x"));
    let a: Among<i32, &str, bool> = nested.into();
    assert_eq!(a, Middle("x"));
    let nested: Either<i32, Either<&str, bool>> = Either::Right(Either::Right(true));
    let a: Among<i32, &str, bool> = nested.into();
    assert_eq!(a, Right(true));

    // Plain Either<A, B> -> Among
    let e: Either<i32, &str> = Either::Left(1);
    let a: Among<i32, &str, ()> = e.into();
    assert_eq!(a, Left(1));
    let e: Either<i32, &str> = Either::Right("x");
    let a: Among<i32, &str, ()> = e.into();
    assert_eq!(a, Middle("x"));
  }

  #[test]
  fn either_ok_err_ext() {
    use among::{EitherErrExt, EitherOkExt};

    let r: Result<Either<i32, i32>, &str> = Ok(Either::Left(2));
    let r = r.map_left(|x| x + 1);
    assert_eq!(r, Ok(Either::Left(3)));

    let r: Result<Either<i32, i32>, &str> = Ok(Either::Right(2));
    let r = r.map_right(|x| x + 1);
    assert_eq!(r, Ok(Either::Right(3)));

    let r: Result<i32, Either<&str, &str>> = Err(Either::Right("e"));
    let r = r.map_err_right(|s| s.len());
    assert_eq!(r, Err(Either::Right(1)));
  }
}

// --- serde feature --------------------------------------------------------

#[cfg(feature = "serde")]
mod serde_feature {
  use super::*;

  #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq)]
  #[serde(transparent)]
  struct Wrap {
    #[serde(with = "among::serde_untagged")]
    inner: Among<u32, String, bool>,
  }

  #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq)]
  #[serde(transparent)]
  struct WrapOpt {
    #[serde(with = "among::serde_untagged_optional")]
    inner: Option<Among<u32, String, bool>>,
  }

  #[test]
  fn untagged_roundtrip_all_variants() {
    let l = Wrap { inner: Left(42) };
    let s = serde_json::to_string(&l).unwrap();
    assert_eq!(s, "42");
    let back: Wrap = serde_json::from_str(&s).unwrap();
    assert_eq!(back, l);

    let m = Wrap {
      inner: Middle("hi".to_string()),
    };
    let s = serde_json::to_string(&m).unwrap();
    assert_eq!(s, "\"hi\"");
    let back: Wrap = serde_json::from_str(&s).unwrap();
    assert_eq!(back, m);

    let r = Wrap { inner: Right(true) };
    let s = serde_json::to_string(&r).unwrap();
    assert_eq!(s, "true");
    let back: Wrap = serde_json::from_str(&s).unwrap();
    assert_eq!(back, r);
  }

  #[test]
  fn untagged_deserialize_error() {
    // None of u32/String/bool should match an array
    let r: Result<Wrap, _> = serde_json::from_str("[1,2,3]");
    assert!(r.is_err());
  }

  #[test]
  fn untagged_optional_roundtrip_all_variants() {
    let l = WrapOpt {
      inner: Some(Left(42)),
    };
    let s = serde_json::to_string(&l).unwrap();
    assert_eq!(s, "42");
    let back: WrapOpt = serde_json::from_str(&s).unwrap();
    assert_eq!(back, l);

    let m = WrapOpt {
      inner: Some(Middle("hi".to_string())),
    };
    let s = serde_json::to_string(&m).unwrap();
    assert_eq!(s, "\"hi\"");
    let back: WrapOpt = serde_json::from_str(&s).unwrap();
    assert_eq!(back, m);

    let r = WrapOpt {
      inner: Some(Right(true)),
    };
    let s = serde_json::to_string(&r).unwrap();
    assert_eq!(s, "true");
    let back: WrapOpt = serde_json::from_str(&s).unwrap();
    assert_eq!(back, r);

    let none = WrapOpt { inner: None };
    let s = serde_json::to_string(&none).unwrap();
    assert_eq!(s, "null");
    let back: WrapOpt = serde_json::from_str(&s).unwrap();
    assert_eq!(back, none);
  }

  #[test]
  fn untagged_optional_deserialize_error() {
    let r: Result<WrapOpt, _> = serde_json::from_str("[1,2,3]");
    assert!(r.is_err());
  }

  #[test]
  fn derived_serde_roundtrip_default_tagged() {
    // The Among type itself derives Serialize/Deserialize externally tagged.
    let l: Among<u32, &str, bool> = Left(1);
    let s = serde_json::to_string(&l).unwrap();
    let back: Among<u32, String, bool> = serde_json::from_str(&s).unwrap();
    assert_eq!(back, Left(1));

    let m: Among<u32, &str, bool> = Middle("x");
    let s = serde_json::to_string(&m).unwrap();
    let back: Among<u32, String, bool> = serde_json::from_str(&s).unwrap();
    assert_eq!(back, Middle("x".to_string()));

    let r: Among<u32, &str, bool> = Right(true);
    let s = serde_json::to_string(&r).unwrap();
    let back: Among<u32, String, bool> = serde_json::from_str(&s).unwrap();
    assert_eq!(back, Right(true));
  }
}

// --- futures-io feature ---------------------------------------------------

#[cfg(all(feature = "futures", feature = "std"))]
mod futures_feature {
  use super::*;
  use core::{
    pin::Pin,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
  };
  use futures_io::{AsyncBufRead, AsyncRead, AsyncSeek, AsyncWrite};
  use std::io::SeekFrom;

  fn noop_waker() -> Waker {
    fn clone(_: *const ()) -> RawWaker {
      RawWaker::new(core::ptr::null(), &VTABLE)
    }
    fn noop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
  }

  /// A trivial type implementing all four async traits with deterministic Ready outputs.
  #[derive(Default)]
  struct Stub {
    pos: u64,
  }

  impl AsyncRead for Stub {
    fn poll_read(
      self: Pin<&mut Self>,
      _cx: &mut Context<'_>,
      buf: &mut [u8],
    ) -> Poll<std::io::Result<usize>> {
      if !buf.is_empty() {
        buf[0] = 1;
        Poll::Ready(Ok(1))
      } else {
        Poll::Ready(Ok(0))
      }
    }
  }
  impl AsyncBufRead for Stub {
    fn poll_fill_buf(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<std::io::Result<&[u8]>> {
      Poll::Ready(Ok(&[]))
    }
    fn consume(self: Pin<&mut Self>, _amt: usize) {}
  }
  impl AsyncWrite for Stub {
    fn poll_write(
      self: Pin<&mut Self>,
      _cx: &mut Context<'_>,
      buf: &[u8],
    ) -> Poll<std::io::Result<usize>> {
      Poll::Ready(Ok(buf.len()))
    }
    fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
      Poll::Ready(Ok(()))
    }
    fn poll_close(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
      Poll::Ready(Ok(()))
    }
  }
  impl AsyncSeek for Stub {
    fn poll_seek(
      mut self: Pin<&mut Self>,
      _cx: &mut Context<'_>,
      pos: SeekFrom,
    ) -> Poll<std::io::Result<u64>> {
      if let SeekFrom::Start(p) = pos {
        self.pos = p;
      }
      Poll::Ready(Ok(self.pos))
    }
  }

  fn poll_all(among_pin: Pin<&mut Among<Stub, Stub, Stub>>, cx: &mut Context<'_>) {
    // We can't reuse the same Pin twice. Helper avoids that by re-projecting.
    let _ = among_pin;
    let _ = cx;
  }

  #[test]
  fn futures_async_traits_each_variant() {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);

    for kind in 0..3u8 {
      let mut among: Among<Stub, Stub, Stub> = match kind {
        0 => Left(Stub::default()),
        1 => Middle(Stub::default()),
        _ => Right(Stub::default()),
      };

      // poll_read
      {
        let mut buf = [0u8; 4];
        let pinned = Pin::new(&mut among);
        match AsyncRead::poll_read(pinned, &mut cx, &mut buf) {
          Poll::Ready(Ok(n)) => assert_eq!(n, 1),
          _ => panic!("unexpected"),
        }
      }
      // poll_fill_buf
      {
        let pinned = Pin::new(&mut among);
        match AsyncBufRead::poll_fill_buf(pinned, &mut cx) {
          Poll::Ready(Ok(slice)) => assert!(slice.is_empty()),
          _ => panic!("unexpected"),
        }
      }
      // consume
      {
        let pinned = Pin::new(&mut among);
        AsyncBufRead::consume(pinned, 0);
      }
      // poll_write
      {
        let pinned = Pin::new(&mut among);
        match AsyncWrite::poll_write(pinned, &mut cx, b"abc") {
          Poll::Ready(Ok(n)) => assert_eq!(n, 3),
          _ => panic!(),
        }
      }
      // poll_flush
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncWrite::poll_flush(pinned, &mut cx);
      }
      // poll_close
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncWrite::poll_close(pinned, &mut cx);
      }
      // poll_seek
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncSeek::poll_seek(pinned, &mut cx, SeekFrom::Start(0));
      }

      poll_all(Pin::new(&mut among), &mut cx);
    }
  }
}

// --- tokio feature --------------------------------------------------------

#[cfg(feature = "tokio")]
mod tokio_feature {
  use super::*;
  use core::{
    pin::Pin,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
  };
  use std::io::SeekFrom;
  use tokio::io::{AsyncBufRead, AsyncRead, AsyncSeek, AsyncWrite, ReadBuf};

  fn noop_waker() -> Waker {
    fn clone(_: *const ()) -> RawWaker {
      RawWaker::new(core::ptr::null(), &VTABLE)
    }
    fn noop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
  }

  #[derive(Default)]
  struct Stub {
    pos: u64,
  }

  impl AsyncRead for Stub {
    fn poll_read(
      self: Pin<&mut Self>,
      _cx: &mut Context<'_>,
      buf: &mut ReadBuf<'_>,
    ) -> Poll<std::io::Result<()>> {
      if buf.remaining() > 0 {
        buf.put_slice(&[1u8]);
      }
      Poll::Ready(Ok(()))
    }
  }
  impl AsyncBufRead for Stub {
    fn poll_fill_buf(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<std::io::Result<&[u8]>> {
      Poll::Ready(Ok(&[]))
    }
    fn consume(self: Pin<&mut Self>, _amt: usize) {}
  }
  impl AsyncWrite for Stub {
    fn poll_write(
      self: Pin<&mut Self>,
      _cx: &mut Context<'_>,
      buf: &[u8],
    ) -> Poll<std::io::Result<usize>> {
      Poll::Ready(Ok(buf.len()))
    }
    fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
      Poll::Ready(Ok(()))
    }
    fn poll_shutdown(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
      Poll::Ready(Ok(()))
    }
  }
  impl AsyncSeek for Stub {
    fn start_seek(mut self: Pin<&mut Self>, pos: SeekFrom) -> std::io::Result<()> {
      if let SeekFrom::Start(p) = pos {
        self.pos = p;
      }
      Ok(())
    }
    fn poll_complete(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<std::io::Result<u64>> {
      Poll::Ready(Ok(self.pos))
    }
  }

  #[test]
  fn tokio_async_traits_each_variant() {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);

    for kind in 0..3u8 {
      let mut among: Among<Stub, Stub, Stub> = match kind {
        0 => Left(Stub::default()),
        1 => Middle(Stub::default()),
        _ => Right(Stub::default()),
      };

      let mut buf_storage = [0u8; 4];
      {
        let mut buf = ReadBuf::new(&mut buf_storage);
        let pinned = Pin::new(&mut among);
        let _ = AsyncRead::poll_read(pinned, &mut cx, &mut buf);
      }
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncBufRead::poll_fill_buf(pinned, &mut cx);
      }
      {
        let pinned = Pin::new(&mut among);
        AsyncBufRead::consume(pinned, 0);
      }
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncWrite::poll_write(pinned, &mut cx, b"hi");
      }
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncWrite::poll_flush(pinned, &mut cx);
      }
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncWrite::poll_shutdown(pinned, &mut cx);
      }
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncSeek::start_seek(pinned, SeekFrom::Start(0));
      }
      {
        let pinned = Pin::new(&mut among);
        let _ = AsyncSeek::poll_complete(pinned, &mut cx);
      }
    }
  }
}
