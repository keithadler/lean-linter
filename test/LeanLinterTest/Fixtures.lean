/-!
One example of every problem `lean-linter` reports, and a correct twin of each that it must not
report. `test/run.sh` checks the output against `test/expected.tsv`.
-/

namespace Fixtures

universe u

/-! ## `mislabel` -/

def fooLeft (n : Nat) : Nat := n
def fooRight (n : Nat) : Nat := n + 1

/-- Copied from `fooRight_zero` and never renamed: it is about `fooRight`. -/
theorem fooLeft_eq (n : Nat) : fooRight n = n + 1 := rfl
theorem fooRight_zero : fooRight 0 = 1 := rfl

/-! ## `namespace` -/

structure Box8 where x : Nat
structure Box16 where x : Nat

theorem Box16.x_self (b : Box8) : b.x = b.x := rfl
theorem Box8.x_add_zero (b : Box8) : b.x + 0 = b.x := rfl

/-! ## `name-shape` -/

def F (n : Nat) : Nat := n

theorem F_injective : Function.Surjective F := fun b => ⟨b, rfl⟩
theorem F_surjective : Function.Surjective F := fun b => ⟨b, rfl⟩
theorem le_self_add_three_iff (n : Nat) : n ≤ n + 3 := by omega
theorem le_self_succ_lt (n : Nat) : n ≤ n + 1 := Nat.le_succ n
theorem self_lt_succ_lt (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-! ## `doc-mislabel` -/

/-- `F` is injective. -/
theorem F_surj : Function.Surjective F := fun b => ⟨b, rfl⟩
/-- `F` is surjective. -/
theorem F_surj' : Function.Surjective F := fun b => ⟨b, rfl⟩

/-! ## `doc-refs` -/

/-- Follows from `Fixtures.no_such_lemma_here`; see also `Fixtures.F_surjective`. -/
theorem docref_demo : 0 < 1 := Nat.zero_lt_one

/-! ## `deprecation` -/

theorem dep_new : 0 < 2 := Nat.zero_lt_succ 1
@[deprecated dep_new (since := "2026-01-01")] theorem dep_mid : True := trivial
@[deprecated dep_mid (since := "2026-01-01")] theorem dep_old : True := trivial

/-! ## `duplicate` and `duplicate-sym` -/

theorem dup_a (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem dup_b (x y : Nat) : x + y = y + x := by omega
theorem sym_a (a : Nat) : a + 0 = a := Nat.add_zero a
theorem sym_b (a : Nat) : a = a + 0 := by omega
/-- Not a duplicate: proved from `dup_a`, as an alias would be. -/
theorem dup_c (a b : Nat) : a + b = b + a := dup_a a b

/-! ## `duplicate-instance` -/

class Pointed (α : Type u) where pt : α
instance pointedNatA : Pointed Nat := ⟨0⟩
instance pointedNatB : Pointed Nat := ⟨1⟩
instance pointedBool : Pointed Bool := ⟨true⟩

/-! ## `dead-private` -/

private theorem unused_helper : 1 + 1 = 2 := rfl
private theorem used_helper : 2 + 2 = 4 := rfl
theorem uses_helper : 2 + 2 = 4 := used_helper

/-! ## `op-mismatch` -/

theorem swapped_mul_law (a b c : Nat) : a + b + c = c + b + a := by omega
theorem swapped_add_law (a b c : Nat) : a + b + c = b + a + c := by omega

/-! ## `vacuous` -/

theorem vac_stmt : True := trivial
theorem clash_hyps (p : Prop) (h : p) (h' : ¬p) : 1 = 2 := absurd h h'
theorem ok_hyps (p q : Prop) (h : p) (h' : q) : p ∧ q := ⟨h, h'⟩

/-! ## `universe` -/

theorem restricted_univ {α : Type} (a : α) : Nonempty α := ⟨a⟩
theorem general_univ {α : Type u} (a : α) : Nonempty α := ⟨a⟩

/-! ## `doc-iff` -/

/-- A number is positive if and only if it is nonzero. -/
theorem doc_iff_demo (n : Nat) (h : 0 < n) : n ≠ 0 := by omega
/-- A number is positive if and only if it is nonzero. -/
theorem doc_iff_ok (n : Nat) : 0 < n ↔ n ≠ 0 := by omega

end Fixtures
