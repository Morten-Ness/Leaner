import Mathlib

variable {R : Type u}

theorem Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [Nontrivial R] {a : R} :
    Odd a → 0 < a := by
  rintro ⟨k, rfl⟩; simp

