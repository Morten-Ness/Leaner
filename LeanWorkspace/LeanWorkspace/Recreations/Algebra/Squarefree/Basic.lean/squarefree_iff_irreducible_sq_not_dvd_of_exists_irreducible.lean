import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R}
    (hr : ∃ x : R, Irreducible x) : Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ← not_exists]
  simp only [hr, not_true, false_or, and_false]

