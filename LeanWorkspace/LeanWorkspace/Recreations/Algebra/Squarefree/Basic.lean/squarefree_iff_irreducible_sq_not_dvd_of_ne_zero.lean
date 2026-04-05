import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r ≠ 0) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm

