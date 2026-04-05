import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

set_option backward.isDefEq.respectTransparency false in
theorem _root_.LieIdeal.isLieAbelian_iff {I : LieIdeal R L} :
    IsLieAbelian I ↔ I ≤ LieModule.ker R L I := by
  refine ⟨fun hI x hx ↦ LieHom.mem_ker.mpr ?_, fun h ↦ ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ?_⟩⟩
  · ext y
    have := IsTrivial.trivial (⟨x, hx⟩ : I) y
    rw [LieIdeal.coe_bracket_of_module] at this
    simp [this]
  · simpa using LinearMap.congr_fun (h hx) ⟨y, hy⟩

