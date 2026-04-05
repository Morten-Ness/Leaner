import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable (R) [CommSemiring R]

theorem mem_gradeBy_iff (f : M → ι) (i : ι) (a : R[M]) :
    a ∈ gradeBy R f i ↔ (a.support : Set M) ⊆ f ⁻¹' {i} := by rfl

