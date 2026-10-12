# lean-linter

**Find what the type checker cannot: lemmas whose names say the opposite of their statements,
docstrings that describe the wrong property or point at declarations that no longer exist,
deprecations that lead to other deprecations, things stated twice, and private code nothing uses.**

Lean checks that every proof is correct. It does not check that `foo_left` is about the left,
that a lemma called `_iff` is an `↔`, or that the name in a docstring still exists. Those mistakes
compile, pass CI, and send the next person looking for a lemma to the wrong one. `lean-linter`
reads a compiled library and reports them.

It works on any Lean 4 project, depends only on Lean, and runs on all of Mathlib (330,000
declarations) in about six minutes.

## What it finds

Run on Mathlib and on Lean's own library in October 2026, it found, among others:

- `HoCat.homEquivLeft_symm_apply` stated a fact about `homEquivRight`: a copy of the lemma above
  it that kept its statement, so the simp lemma for `homEquivLeft` did not exist.
- `AntitoneOn.monotone` concludes `Antitone`, and `PresheafOfModules.mono_iff_surjective` states
  that `f` is mono iff it is *injective* on every object.
- `DFinsupp.coe_strictMono` and `Finsupp.coe_strictMono` are copies of `coe_mono`. They conclude
  plain `Monotone`, so the strict lemma their names promise does not exist.
- `reflexivePair_map_left` and `reflexivePair_map_right` have their names swapped.
- Three instances in the `CommMonCat` namespace state that the forgetful functor of `MonCat`
  creates limits. They were copied from `MonCat`, so the `CommMonCat` instances are missing.
- In Lean core, `Std.Roc.lower_le_of_mem` (and its `Roo`, `Roi` twins) concludes `r.lower < a`,
  and `List.findIdx?_eq_fst_find?_zipIdx` uses `.2`, the second component.

## Quick start

In a Lake project, add the dependency to `lakefile.toml`:

```toml
[[require]]
name = "lean-linter"
git = "https://github.com/keithadler/lean-linter"
rev = "v0.3.0"
```

Then build your library and lint it:

```bash
lake build
lake exe lean-linter MyLibrary
```

To lint a project you don't want to change, Mathlib say, build lean-linter with the same Lean
version as the project, then run it from the project's directory so it finds the project's
`.olean` files:

```bash
git clone https://github.com/keithadler/lean-linter && cd lean-linter
cp ../mathlib4/lean-toolchain . && lake build
cd ../mathlib4 && lake env ../lean-linter/.lake/build/bin/lean-linter Mathlib
```

## Output

One finding per line: check, declaration, `Module:line`, and what is wrong.

```text
mislabel     Fixtures.fooLeft_eq       LeanLinterTest.Fixtures:13   the name says `Fixtures.fooLeft` but the statement uses `Fixtures.fooRight` and never `fooLeft`
name-shape   Fixtures.le_self_succ_lt  LeanLinterTest.Fixtures:32   the name ends in `_lt` (strict), but the conclusion is a `≤`
doc-refs     Fixtures.docref_demo      LeanLinterTest.Fixtures:44   the docstring mentions `Fixtures.no_such_lemma_here`, which does not exist
deprecation  Fixtures.dep_old          LeanLinterTest.Fixtures:51   deprecated in favor of `Fixtures.dep_mid`, which is itself deprecated
```

The real output separates fields with tabs. A summary with one count per check goes to
standard error, so `lean-linter MyLib > findings.tsv` keeps the two apart. With `--json`, each
finding is one JSON object per line instead:

```json
{"check":"deprecation","declaration":"Fixtures.dep_old","line":51,"message":"deprecated in favor of `Fixtures.dep_mid`, which is itself deprecated","module":"LeanLinterTest.Fixtures"}
```

## Checks

| Check | Reports | Example |
|---|---|---|
| `mislabel` | The name names a constant, but the statement uses only its opposite (`Left`/`Right`, `fst`/`snd`, `inl`/`inr`, `Monotone`/`Antitone`, `map`/`comap`, ...). | `fooLeft_eq : fooRight n = n + 1` |
| `namespace` | In the namespace of a type, but stated about a sibling of that type (`UInt8`/`UInt16`, `WithTop`/`WithBot`, `CommMonCat`/`MonCat`). | `Box16.x_self (b : Box8) : ...` |
| `name-shape` | The last word of the name promises a conclusion the statement does not have: `_iff` with no `↔`, `_lt` concluding `≤`, `_le` concluding `<`, `_injective` concluding `Surjective`. | `F_injective : Function.Surjective F` |
| `doc-mislabel` | The docstring names one property of a family ("injective", "monotone", "open"), the conclusion another. | "`F` is injective." on a surjectivity lemma |
| `doc-refs` | A name in backticks in a docstring matches no declaration, module, tactic, attribute or option. | `` `Nat.not_a_lemma` `` after a rename |
| `deprecation` | Deprecated in favor of a declaration that does not exist or is itself deprecated. Lean already warns about this when the alias is declared, so what this finds are the places someone silenced that warning on purpose (`set_option linter.deprecated.deprecatedTarget false`), usually in the middle of a rename. | `old → mid → new`, with `mid` deprecated |
| `duplicate` | Two theorems with the same statement (up to the names of variables and universes), each proved without the other. | the same lemma proved in two files |
| `duplicate-sym` | The same, with one stated backwards: `a = b` against `b = a`. | `x + 0 = x` and `x = x + 0` |
| `duplicate-instance` | Two instances of the same type. | two `Pointed Nat` instances |
| `dead-private` | A private theorem or definition that nothing refers to. | a helper left behind by a refactor |
| `vacuous` | A statement that says nothing: conclusion `True`, a hypothesis `False`, or two hypotheses `p` and `¬p`. Both sides of an `=` being the same term is reported too, since it is usually an abbreviation-unfolding lemma and sometimes a lemma that proves nothing. | `foo (h : p) (h' : ¬p) : 1 = 2` |
| `universe` | A public theorem or definition with a binder `α : Type` and no universe parameters, so it cannot be used for a type in a higher universe. A file with eight or more is reported once. | `{R : Type}` where its neighbors say `Type*` |
| `op-mismatch` *(experimental)* | The name says `add`, `mul`, `sub`, `div`, `sum` or `prod`, but the statement uses none of it and uses a confusable one instead. Mathlib's naming is loose enough that most hits are legitimate. | `foo_mul_comm : a + b = b + a` |
| `doc-iff` *(experimental)* | The docstring says "if and only if", but the statement is not an `↔`. Many hits are docstrings written for the iff version of a lemma that give one direction. | "`n` is positive iff nonzero" on `0 < n → n ≠ 0` |
| `trust` | What the declaration asks you to believe besides Lean's kernel: `sorry`, a user `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, an `opaque` constant. | `theorem t : 3 + 3 = 6 := sorry` |
| `diamond` | Two instances of one type that are not definitionally equal, so instance search picks one by import order. | two `Wit Bool` instances giving different values |
| `proof-clone` | Two theorems that state different things, whose compiled proofs apply the same five or more lemmas in the same order: an argument copied and edited, for `Array` and for `Vector`, or for a statement and the same with one more hypothesis. Tactic-written terms are mostly too different to match. | `any_eq'` for `Array` and for `Vector` |

`lean-linter --list` prints the checks; `--checks mislabel,doc-refs` runs only some.

Only declarations written by hand are checked. Equation lemmas, matchers, recursors, auxiliary
proofs and anything else Lean generates are skipped, and so are deprecated declarations. A theorem
proved from the other one (an `alias`, a `.symm`) is a deliberate second name and is never reported
as a duplicate.

## Options

```text
lean-linter [options] Module...

  --checks a,b,...   run only these checks (see --list)
  --root Prefix      report on modules under Prefix (repeatable); the default is the first
                     component of each module given, e.g. Mathlib for Mathlib.Order.Basic
  --json             print findings as JSON lines instead of tab-separated text
  --list             list the checks and exit
  --version          print the version and exit
```

The exit status is 0 if nothing was found, 1 if something was, and 2 on a usage error.

## Reading the findings

The checks compare names and docstrings with statements, and English is looser than Lean, so
each finding is something to read rather than a verdict.

- **`mislabel`, `namespace`, `name-shape`, `doc-mislabel`, `duplicate-instance`**
  are usually right. The exceptions are words with a second meaning: `_odd` naming the parity of
  an index, "limit" meaning a limit ordinal, `pred` meaning `n - 1`.
- **`vacuous`** found nothing wrong in Mathlib or Lean core: its few hits are tactic-internal lemmas. That is the point of running it, on a formalization someone else wrote and you want to trust.
- **`trust`** lists a project's to-do list (`sorry`, axioms, `native_decide`). On Mathlib it reports only `opaque` and `unsafe` declarations, which are meta-programming code, and no `sorry`, axiom or `native_decide`.
- **`diamond`** found no instance diamonds in Mathlib: every same-typed pair it compared is definitionally equal.
- **`proof-clone`** is exact about what it compares, which is the lemmas a proof applies and their order, not whether two arguments are the same. Run on Lean core it lists 247 groups, most of them one argument made for two types, which is by design in a library with parallel `Array` and `Vector` APIs. The fix is usually a shared lemma, or to leave it.
- **`universe`** is usually right once tactic, meta-programming and private code is left out. Some small-category statements need `Type` on purpose.
- **`op-mismatch`, `doc-iff`** are experimental. On Mathlib `op-mismatch` gives about sixty hits of which a handful are real name errors, and `doc-iff` mostly flags docstrings that describe an iff the lemma is one half of.
- **`duplicate`, `duplicate-sym`** are exact, but some duplication is on purpose: a second name for
  dot notation or for people searching under another name. The usual fix is to make one an
  `alias` of the other, which this check then accepts.
- **`doc-refs`, `dead-private`** find real rot, mixed with things they cannot see through: notation
  written in backticks, and lemmas used by a tactic that looks them up by name (`aesop` rules,
  `simproc`s) without any term mentioning them.

- **`deprecation`** only reports aliases whose authors switched off Lean's own warning, so on a library that heeds that warning it is nearly silent, and on Mathlib every hit was a rename in progress.

On Mathlib a full run gives a few dozen findings for the first group and hundreds for the others.
Lean core gives a handful for the first group.

## How it works

`lean-linter` imports the modules you name, the way `lean` does when it elaborates a file that
imports them. It then reads the resulting environment: every declaration's statement, proof,
docstring, source position and attributes. Nothing is parsed or elaborated again, so the checks
see exactly what Lean compiled, including declarations generated by attributes such as
`to_additive` and `simps`. It needs the library to be built first.

Because it reads `.olean` files, lean-linter has to be built with the same Lean version as the
library it reads. As a dependency it is built with your project's toolchain automatically; on its
own, copy the project's `lean-toolchain` before building, as in the quick start. Development
happens on Lean v4.35.0-rc4.

| Library | Declarations | Time |
|---|---|---|
| Lean core (`Init`, `Std`, `Lean`) | 99,000 | ~10 s |
| Mathlib | 330,000 | ~6 min |

## In CI

Run lean-linter on pull requests and keep only what is new by comparing against a saved baseline:

```yaml
- name: Lint
  run: |
    lake exe lean-linter MyLibrary > findings.tsv || true
    cut -f1,2 findings.tsv | sort > now.txt
    sort lint-baseline.txt | comm -13 - now.txt > new.txt
    if [ -s new.txt ]; then cat new.txt; exit 1; fi
```

## Development

```bash
lake build          # the library and the lean-linter executable
./test/run.sh       # every check against test/LeanLinterTest/Fixtures.lean
```

`test/LeanLinterTest/Fixtures.lean` has one example of each problem and a correct twin of each.
`test/run.sh` checks that the linter reports exactly the examples, as listed in
`test/expected.tsv`.

To add a check, write `def myCheck : Check` in a new file under `LeanLinter/Checks/`. Its
module docstring should explain what it reports, how it decides, and its known false positives.
Then add it to `allChecks` in `LeanLinter.lean`, and give it an example and a correct twin in the
fixtures.

## License

Apache License 2.0. See [LICENSE](LICENSE).
