import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable {f : L →ₗ⁅R⁆ L'} {I I₂ : LieIdeal R L} {J : LieIdeal R L'}

theorem map_sup_ker_eq_map : LieIdeal.map f (I ⊔ f.ker) = LieIdeal.map f I := by
  refine le_antisymm ?_ (LieIdeal.map_mono le_sup_left)
  apply LieSubmodule.lieSpan_mono
  rintro x ⟨y, hy₁, hy₂⟩
  rw [← hy₂]
  erw [LieSubmodule.mem_sup] at hy₁
  obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁
  rw [← hy]
  rw [map_add, f.coe_toLinearMap, LieHom.mem_ker.mp hz₂, add_zero]; exact ⟨z₁, hz₁, rfl⟩

