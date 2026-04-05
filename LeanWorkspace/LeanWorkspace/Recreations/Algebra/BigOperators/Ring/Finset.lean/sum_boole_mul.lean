import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonAssocSemiring R] [DecidableEq ι]

theorem sum_boole_mul (s : Finset ι) (f : ι → R) (i : ι) :
    ∑ j ∈ s, ite (i = j) 1 0 * f j = ite (i ∈ s) (f i) 0 := by simp

