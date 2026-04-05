import Mathlib

variable {ι : Type*}

variable {R : Type*}

theorem SetLike.one_mem_graded {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : (1 : R) ∈ A 0 := SetLike.GradedOne.one_mem

