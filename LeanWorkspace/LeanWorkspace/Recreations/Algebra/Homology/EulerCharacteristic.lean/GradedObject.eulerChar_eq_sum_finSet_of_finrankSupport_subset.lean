import Mathlib

variable {R : Type*} [Ring R] {ι : Type*}

variable (c : ComplexShape ι) [c.EulerCharSigns]

private theorem support_eulerChar_summand (X : CategoryTheory.GradedObject ι (ModuleCat R)) :
    Function.support (fun i => (c.χ i : ℤ) * Module.finrank R (X i)) = GradedObject.finrankSupport X := by
  simp only [GradedObject.finrankSupport, Function.support_mul_of_ne_zero_left (fun i => Units.ne_zero (c.χ i))]
  ext i; simp [Function.mem_support]


theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (X : CategoryTheory.GradedObject ι (ModuleCat R)) (indices : Finset ι)
    (h_support : GradedObject.finrankSupport X ⊆ indices) :
    GradedObject.eulerChar c X = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (X i) := by
  simp only [GradedObject.eulerChar]
  rw [finsum_eq_sum_of_support_subset]
  exact (support_eulerChar_summand c X).symm ▸ h_support

