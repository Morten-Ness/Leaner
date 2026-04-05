import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (t : R) (x y z : L) (m n : M)

variable {ι κ : Type*}

theorem sum_lie_sum {κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → L) (g : κ → M) :
    ⁅(∑ i ∈ s, f i), ∑ j ∈ t, g j⁆ = ∑ i ∈ s, ∑ j ∈ t, ⁅f i, g j⁆ := by
  simp_rw [sum_lie, lie_sum]

