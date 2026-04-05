import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem isIdealMorphism_iff : f.IsIdealMorphism ↔ ∀ (x : L') (y : L), ∃ z : L, ⁅x, f y⁆ = f z := by
  simp only [LieHom.isIdealMorphism_def, LieHom.idealRange_eq_lieSpan_range, ←
    LieSubalgebra.toSubmodule_inj, ← f.range.coe_toSubmodule,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff,
    LieSubalgebra.mem_toSubmodule, mem_range, exists_imp,
    Submodule.exists_lieSubmodule_coe_eq_iff]
  constructor
  · intro h x y; obtain ⟨z, hz⟩ := h x (f y) y rfl; use z; exact hz.symm
  · intro h x y z hz; obtain ⟨w, hw⟩ := h x z; use w; rw [← hw, hz]

