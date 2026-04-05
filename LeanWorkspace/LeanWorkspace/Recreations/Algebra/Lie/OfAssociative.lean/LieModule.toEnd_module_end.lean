import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem LieModule.toEnd_module_end :
    LieModule.toEnd R (Module.End R M) M = LieHom.id := by ext g m; simp [lie_eq_smul]

