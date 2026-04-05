import Mathlib

variable {R : Type*} [Ring R] {ι : Type*}

variable (c : ComplexShape ι) [c.EulerCharSigns]

theorem finrankSupport_subset_iff (X : CategoryTheory.GradedObject ι (ModuleCat R)) (s : Set ι) :
    GradedObject.finrankSupport X ⊆ s ↔ ∀ i ∉ s, Module.finrank R (X i) = 0 := Function.support_subset_iff'

