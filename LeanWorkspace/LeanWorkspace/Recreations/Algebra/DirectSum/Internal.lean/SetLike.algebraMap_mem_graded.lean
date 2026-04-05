import Mathlib

variable {ι : Type*} {σ S R : Type*}

theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R s ∈ A 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (A 0).smul_mem s <| SetLike.one_mem_graded _

