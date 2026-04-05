import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_le_iff_le_comap {f : M →ₙ* N} {S : Subsemigroup M} {T : Subsemigroup N} :
    S.map f ≤ T ↔ S ≤ T.comap f := image_subset_iff

