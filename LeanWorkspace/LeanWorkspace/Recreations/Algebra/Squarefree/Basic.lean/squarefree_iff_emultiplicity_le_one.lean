import Mathlib

variable {R : Type*}

theorem squarefree_iff_emultiplicity_le_one [CommMonoid R] (r : R) :
    Squarefree r ↔ ∀ x : R, emultiplicity x r ≤ 1 ∨ IsUnit x := by
  refine forall_congr' fun a => ?_
  rw [← sq, pow_dvd_iff_le_emultiplicity, or_iff_not_imp_left, not_le, imp_congr _ Iff.rfl]
  norm_cast
  rw [← one_add_one_eq_two]
  exact Order.add_one_le_iff_of_not_isMax (by simp)

