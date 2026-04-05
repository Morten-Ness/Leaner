import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    comap f ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ = ⁅comap f J₁, comap f J₂⁆ ⊔ f.ker := by
  rw [← LieSubmodule.toSubmodule_inj, comap_toSubmodule,
    LieSubmodule.sup_toSubmodule, f.ker_toSubmodule, ← Submodule.comap_map_eq,
    LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LinearMap.map_span]
  congr
  ext
  simp_all only [Subtype.exists, LieSubmodule.mem_inf, LieHom.mem_idealRange_iff, exists_prop,
    Set.mem_setOf_eq, LieHom.coe_toLinearMap, mem_comap,
    exists_exists_and_exists_and_eq_and, LieHom.map_lie]
  grind

