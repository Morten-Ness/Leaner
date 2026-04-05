import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonAssocSemiring R] [DecidableEq ι]

theorem sum_mul_boole (s : Finset ι) (f : ι → R) (i : ι) :
    ∑ j ∈ s, f j * ite (i = j) 1 0 = ite (i ∈ s) (f i) 0 := by simp

