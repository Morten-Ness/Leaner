import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable {f : L →ₗ⁅R⁆ L'} {I I₂ : LieIdeal R L} {J : LieIdeal R L'}

theorem bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥) :
    I = ⊥ := by
  rw [← LieHom.ker_eq_bot f, LieHom.ker] at h₁
  rw [eq_bot_iff, LieIdeal.map_le_iff_le_comap, h₁] at h₂
  rw [eq_bot_iff]; exact h₂

