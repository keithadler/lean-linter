# lean-linter

Linters for Lean 4 libraries that read the compiled environment and report what the type checker
cannot see: lemmas whose names say the opposite of their statements, docstrings that point at
declarations that no longer exist, deprecations that lead to other deprecations, things stated or
defined twice, and private code nothing uses.

It works on any Lean project and depends only on Lean itself.

## Checks

| Check | Reports |
|---|---|
| `mislabel` | A lemma whose name names a constant (`homEquivLeft`, `fst`, `inl`, `Monotone`) while its statement uses only that constant's opposite (`homEquivRight`, `snd`, `inr`, `Antitone`): usually a copy of its neighbor that kept the neighbor's name. |
| `namespace` | `Foo.bar` in the namespace of a type `Foo` whose statement never mentions `Foo` but is about a sibling of it: `UInt16.x` stated for `UInt8`, a `CommMonCat` instance stated for `MonCat`. |
| `name-shape` | A name ending in `_iff` whose conclusion has no `↔`; `_lt` or `_pos` concluding a `≤`; `_le` or `_nonneg` concluding a `<`; `_injective` concluding `Surjective`, `_monotone` concluding `Antitone`, and so on. Words after `_of_` name hypotheses and are not checked. |
| `doc-mislabel` | A docstring that calls the result one property of a family ("injective", "monotone", "open") when the statement concludes another. |
| `doc-refs` | A name in backticks in a docstring that matches no declaration, module, tactic, attribute or option: usually left behind by a rename. |
| `deprecation` | A deprecated alias whose replacement does not exist or is itself deprecated. |
| `duplicate` | Two theorems with the same statement (up to the names of bound variables and universes), each proved without the other. |
| `duplicate-sym` | The same, with one stating `a = b` (or `a ↔ b`) and the other `b = a`. |
| `duplicate-instance` | Two instances of the same type. |
| `dead-private` | A private theorem or definition that nothing refers to. |

Only declarations written by hand are checked. Equation lemmas, matchers, recursors and other
generated declarations are skipped, as are deprecated ones.

## Use

Add it to your project's `lakefile.toml`:

```toml
[[require]]
name = "lean-linter"
git = "https://github.com/keithadler/lean-linter"
rev = "main"
```

Then, from your project's directory, build your library and run:

```bash
lake build && lake exe lean-linter MyLibrary
```

To run it outside a project, for example on Mathlib, build it here with the same Lean version as
the target, then run it from the target's directory so that it finds the target's `.olean` files:

```bash
cd path/to/mathlib4 && lake env path/to/lean-linter/.lake/build/bin/lean-linter Mathlib
```

Options:

- `--checks mislabel,doc-refs` runs only the named checks.
- `--root Prefix` restricts the report to modules under `Prefix`. The default is the first
  component of each module given.

Each finding is one tab-separated line: check, declaration, `Module:line`, message. A summary goes
to standard error. The exit code is 1 if anything was found.

## How much to trust a finding

The checks are heuristics about names and statements, not proofs. In order of how often a finding
is a real problem:

- `mislabel`, `name-shape`, `doc-mislabel`, `deprecation`, `duplicate-instance` and `namespace`
  find few false positives, but read each one before acting on it. A conclusion about a limit
  ordinal is not about `limit`, and `_odd` can name the parity of an index.
- `duplicate` and `duplicate-sym` are exact, but some duplication is deliberate, such as a second
  name for dot notation or for discoverability. Then the usual fix is to make one an `alias` of
  the other.
- `doc-refs` and `dead-private` find real rot, mixed with notation in backticks and lemmas
  registered for tactics by attributes (`aesop`, simprocs).

## Tests

`test/run.sh` runs every check on `test/LeanLinterTest/Fixtures.lean`. That file has one example of
each problem and a correct twin of each, and the script compares the findings with
`test/expected.tsv`.

## License

Apache License 2.0. See [LICENSE](LICENSE).
