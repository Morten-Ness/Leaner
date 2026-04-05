import Mathlib

variable {ι : Type*}

variable {R S : Type*} [SetLike S R]

theorem SetLike.isHomogeneousElem_one [Zero ι] [One R] (A : ι → S) [SetLike.GradedOne A] :
    SetLike.IsHomogeneousElem A (1 : R) := ⟨0, SetLike.one_mem_graded _⟩

