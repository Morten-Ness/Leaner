import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (t : R) (x y z : L) (m n : M)

variable {ι κ : Type*}

theorem sum_lie (s : Finset ι) (f : ι → L) (m : M) : ⁅∑ i ∈ s, f i, m⁆ = ∑ i ∈ s, ⁅f i, m⁆ := map_sum ((LieRingModule.toEnd L M).flip m) f s

