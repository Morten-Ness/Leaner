import Mathlib

variable {R : Type*} [Ring R] {ι : Type*}

variable {c : ComplexShape ι} [c.EulerCharSigns]

private theorem support_eulerChar_summand (X : CategoryTheory.GradedObject ι (ModuleCat R)) :
    Function.support (fun i => (c.χ i : ℤ) * Module.finrank R (X i)) = GradedObject.finrankSupport X := by
  simp only [GradedObject.finrankSupport, Function.support_mul_of_ne_zero_left (fun i => Units.ne_zero (c.χ i))]
  ext i; simp [Function.mem_support]


theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset (C : HomologicalComplex (ModuleCat R) c)
    (indices : Finset ι)
    (h_support : GradedObject.finrankSupport C.X ⊆ indices) :
    GradedObject.eulerChar C = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (C.X i) := GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c C.X indices h_support

