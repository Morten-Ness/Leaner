import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem comap_bracket_incl_of_le {I₁ I₂ : LieIdeal R L} (h₁ : I₁ ≤ I) (h₂ : I₂ ≤ I) :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I₁, I₂⁆ := by
    rw [LieIdeal.comap_bracket_incl]; rw [← inf_eq_right] at h₁ h₂; rw [h₁, h₂]

