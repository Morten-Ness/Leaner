import Mathlib

variable {ι : Type*} {σ S R : Type*}

theorem SetLike.intCast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
    [AddSubgroupClass σ R] (A : ι → σ) [SetLike.GradedOne A] (z : ℤ) : (z : R) ∈ A 0 := by
  cases z
  · rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact SetLike.natCast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.natCast_mem_graded _ _)

