import Mathlib

variable {ι : Type*} {σ S R : Type*}

theorem SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A : ι → Submodule S R}
    {s : S} {r : R} (hr : SetLike.IsHomogeneousElem A r) : SetLike.IsHomogeneousElem A (s • r) := let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩

