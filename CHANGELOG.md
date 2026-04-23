# 0.2.0 (Apr 23rd, 2026)

BREAKING

- Bump minimum supported Rust version (MSRV) to 1.85.0.

FEATURES

- Make the following borrowing accessors `const fn`: `is_left`, `is_middle`, `is_right`, `as_ref`, `as_mut`, `as_pin_ref`, `as_pin_mut`, `left_ref`, `middle_ref`, `right_ref`, `left_mut`, `middle_mut`, `right_mut`, `Among::<T, T, T>::as_inner` and `Among::<T, T, T>::as_inner_mut`.
- Make `Among::<&L, &M, &R>::copied` and `Among::<&mut L, &mut M, &mut R>::copied` `const fn`.

- Add `Among::is_left_and`, `Among::is_middle_and` and `Among::is_right_and` for predicate-aware variant checks.
- Add `Among::inspect_left`, `Among::inspect_middle` and `Among::inspect_right` for side-effectful observation that passes `self` through.
- Add `Among::left_ref`, `Among::middle_ref`, `Among::right_ref`, `Among::left_mut`, `Among::middle_mut` and `Among::right_mut` as `Option<&_>` / `Option<&mut _>` shortcuts over `as_ref()` / `as_mut()`.
- Add `Among::insert_left`, `Among::insert_middle` and `Among::insert_right` to overwrite `self` with the named variant and return a mutable reference to the new value.
- Add `Among::get_or_insert_left`, `Among::get_or_insert_middle`, `Among::get_or_insert_right` and their lazy `*_with` counterparts.
- Add `Among::try_among_into::<T>` for fallible conversion, preserving the originating side via `Result<T, Among<E_L, E_M, E_R>>`.
- Add `Among::as_inner` and `Among::as_inner_mut` on `Among<T, T, T>` to borrow the contained value without consuming it.

BUG FIXES

- Fix `Among::unwrap_left` panic message to reference `unwrap_left` instead of `unwrap_middle` when invoked on a `Middle` value.
- Fix `Among::unwrap_right` panic message to reference `unwrap_right` instead of `unwrap_middle` when invoked on a `Middle` value.
- Add the missing `(Middle, Middle)` in-place branch to `Clone::clone_from`, so the `Middle` variant reuses its allocation like `Left` and `Right` already do.

DOCS

- Fix `Among::is_middle` doc comment that incorrectly described the `Right` variant.
- Expand the `# Panics` sections on `unwrap_left`, `unwrap_middle` and `unwrap_right` to list both panicking variants.
- Add `# Panics` sections to `Among::into_left_middle`, `Among::into_middle_right` and `Among::into_left_right`.
- Drop stray semicolons after the `struct` definitions in the `serde_untagged` and `serde_untagged_optional` module-level doctests.

TESTS

- Remove the unused `mockvec` write inside the `seek` test's mock-data loop.

# 0.1.8 (Jan 24th, 2026)

FEATURES

- Add `Among::flip_left_middle` and `Among::flip_middle_right` to swap adjacent variants without permuting all three type parameters.
- Add `Among::shift_left` and `Among::shift_right` to rotate the variant in a single direction ([#7](https://github.com/al8n/among/issues/7), [#9](https://github.com/al8n/among/pull/9)).

# 0.1.7 (Oct 14th, 2024)

FEATURES

- Add `Among::try_into_left_middle`, `Among::try_into_middle_right`, `Among::try_into_left_right` and their panicking `into_*` counterparts, gated behind the `either` feature.
- Add `Among::from_either_to_left_right`, `Among::from_either_to_left_middle` and `Among::from_either_to_middle_right`.

# 0.1.6 (Oct 8th, 2024)

FIXES

- Fix `cargo doc` generation (feature gating / `docs.rs` metadata).

# 0.1.5 (Oct 7th, 2024)

FEATURES

- Add `AmongErrorExt` / `AmongOkExt` extension traits for `Result<_, Among<_,_,_>>` and `Result<Among<_,_,_>, _>` with `map_err_{left,middle,right}` and `map_{left,middle,right}` helpers.
- Add `EitherOkExt` / `EitherErrExt` extension traits mirroring the above for `Result<_, Either<_, _>>` and `Result<Either<_, _>, _>`.

# 0.1.4 (Oct 7th, 2024)

CHANGES

- Adjust the `From<Either<A, B>>` blanket impls for `Among` so the three-way conversions compose more ergonomically.

# 0.1.3 (Oct 4th, 2024)

FEATURES

- Additional `either` conversion helpers on top of the 0.1.2 surface.

# 0.1.2 (Sep 14th, 2024)

FEATURES

- Add the `either` feature, introducing `src/either_impl.rs` with the initial `Either` ↔ `Among` conversion API.

# 0.1.1 (Sep 3rd, 2024)

CHANGES

- Reorganise the crate manifest and CI workflow; publish to crates.io.

# 0.1.0 (Sep 3rd, 2024)

FEATURES

- Initial release: the `Among<L, M, R>` sum type with `Left`/`Middle`/`Right` variants and trait impls (`Clone`, `Copy`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Debug`, `Display`, `Error`, `Future`, `Iterator`/`DoubleEndedIterator`/`ExactSizeIterator`/`FusedIterator`, `Read`/`Write`/`Seek`/`BufRead`, `AsRef`/`AsMut`, `Deref`/`DerefMut`, `Extend`).
- Optional `serde` (`serde_untagged`, `serde_untagged_optional`), `futures` (`AsyncRead`/`AsyncBufRead`/`AsyncWrite`/`AsyncSeek`) and `tokio` (`AsyncRead`/`AsyncBufRead`/`AsyncWrite`/`AsyncSeek`) integrations.
- `IntoAmong` trait and `IterAmong` iterator adaptor.
