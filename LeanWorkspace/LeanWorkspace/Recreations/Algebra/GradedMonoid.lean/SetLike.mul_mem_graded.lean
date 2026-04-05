import Mathlib

variable {ι : Type*}

variable {R : Type*}

theorem SetLike.mul_mem_graded {S : Type*} [SetLike S R] [Mul R] [Add ι] {A : ι → S}
    [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi ∈ A i) (hj : gj ∈ A j) : gi * gj ∈ A (i + j) := SetLike.GradedMul.mul_mem hi hj

