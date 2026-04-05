import Mathlib

variable {R : Type*} [Ring R] {ι : Type*}

variable {c : ComplexShape ι} [c.EulerCharSigns]

private theorem support_eulerChar_summand (X : CategoryTheory.GradedObject ι (ModuleCat R)) :
    Function.support (fun i => (c.χ i : ℤ) * Module.finrank R (X i)) = GradedObject.finrankSupport X := by
  simp only [GradedObject.finrankSupport, Function.support_mul_of_ne_zero_left (fun i => Units.ne_zero (c.χ i))]
  ext i; simp [Function.mem_support]


theorem homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    (C : HomologicalComplex (ModuleCat R) c) [∀ i : ι, C.HasHomology i] (indices : Finset ι)
    (h_support : GradedObject.finrankSupport (fun i => C.homology i) ⊆ indices) :
    homologyEulerChar C = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (C.homology i) := GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c
    (fun i => C.homology i) indices h_support

