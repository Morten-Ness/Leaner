import Mathlib

variable {ι : Type*} {σ S R : Type*}

theorem SetLike.homogeneous_zero_submodule [Zero ι] [Semiring S] [AddCommMonoid R] [Module S R]
    (A : ι → Submodule S R) : SetLike.IsHomogeneousElem A (0 : R) := ⟨0, Submodule.zero_mem _⟩

