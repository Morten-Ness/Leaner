import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_insert_natCast (n : ℕ) (s : Set R) : Subsemiring.closure (insert (n : R) s) = Subsemiring.closure s := by
  rw [Set.insert_eq, Subsemiring.closure_union]
  simp

