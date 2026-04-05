import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable {f : L →ₗ⁅R⁆ L'} {I I₂ : LieIdeal R L} {J : LieIdeal R L'}

theorem mem_map_of_surjective {y : L'} (h₁ : Function.Surjective f) (h₂ : y ∈ I.map f) :
    ∃ x : I, f x = y := by
  rw [← LieSubmodule.mem_toSubmodule, LieIdeal.coe_map_of_surjective h₁, Submodule.mem_map] at h₂
  obtain ⟨x, hx, rfl⟩ := h₂
  use ⟨x, hx⟩
  rw [LieHom.coe_toLinearMap]

