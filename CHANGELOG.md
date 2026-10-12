# Changelog

## 0.5.0

`proof-clone` is split in two. On Lean core the 0.4.0 check listed 247 groups, 137 of which were a family of lemmas written on purpose (`sum_push` and `prod_push`, `Array.any_eq'` and `Vector.any_eq'`: names that differ in one word).

- `proof-clone` now lists only the groups whose names differ in more than one word: about 110 on Lean core.
- `proof-variant` lists the one-word families, listed apart.
- Each group is reported at its first theorem in file order, so the output is stable.

## 0.4.0

One new check.

- `proof-clone`: two theorems with different statements whose proofs apply the same lemmas in the same order (five or more, plumbing such as `Eq.symm` and `congrArg` left out). It reads the compiled proof terms, so it is not fooled by renamed variables or reformatted tactic scripts. On Lean core it lists 247 groups.

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
