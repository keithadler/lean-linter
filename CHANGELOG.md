# Changelog

## 0.3.0

Two new checks, and fewer false positives. The fixes come from running the linter on FloatLib, a
numerics library, where every finding in `mislabel` and `name-shape` and most in `doc-refs` was wrong.

Fewer false positives:

- `mislabel`: `¬Even n` says `n` is odd, and `¬Odd n` says it is even, so a lemma named `..._odd` with
  the hypothesis `¬Even n` is no longer reported.
- `name-shape`: `n + 1 ≤ m` (and `Nat.succ n ≤ m`) is how `n < m` is written on `Nat`, so a `_lt` lemma
  concluding it is no longer reported. `_pos` after `mono`, `monotone`, `anti`, `antitone`,
  `strictMono` or `strictAnti` means "on the positives", not "strictly", and is no longer reported.
- `doc-refs`: a docstring that names the declaration's own parameter, a keyword the project adds to
  the grammar, a built-in attribute (`implemented_by`), or a stretch from the middle of a module name
  (`Packed.Product` for `Foo.Packed.Product.Proof`) is no longer reported.

Each of these has a regression fixture in `test/`, and `wrong_odd` stays reported as a control.

Two new checks.

- `trust`: `sorry`, user axioms, `native_decide`, `unsafe`, `implemented_by`, `extern` and `opaque`, so a reader can see what a formalization asks them to believe besides the kernel. On Mathlib it lists only `opaque` and `unsafe` meta-programming code.
- `diamond`: same-typed instances that are not definitionally equal (at instance transparency, then default). None in Mathlib.

## 0.2.0

Four new checks, bringing the total to fourteen.

- `vacuous`: statements that say nothing, such as a conclusion `True`, a hypothesis `False`, or two contradictory hypotheses. Found nothing wrong in Mathlib or Lean core.
- `universe`: public declarations with a binder `α : Type` and no universe parameters, so they cannot be used at a higher universe. A file with eight or more is reported once.
- `op-mismatch` (experimental): a name that says `add`, `mul`, `sub`, `div`, `sum` or `prod` while the statement uses a confusable operation instead.
- `doc-iff` (experimental): a docstring that says "if and only if" on a statement that is not an `↔`.

Also: the README now says which checks are reliable and which are experimental.

## 0.1.0

First release: `mislabel`, `namespace`, `name-shape`, `doc-mislabel`, `doc-refs`, `deprecation`, `duplicate`, `duplicate-sym`, `duplicate-instance` and `dead-private`, with `--checks`, `--root`, `--json`, `--list` and `--version`.
