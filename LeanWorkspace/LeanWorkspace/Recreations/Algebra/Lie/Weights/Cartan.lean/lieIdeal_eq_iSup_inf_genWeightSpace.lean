import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [H.IsCartanSubalgebra] [IsNoetherian R L] (α : H → R)

variable {K : Type*} [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [LieModule.IsTriangularizable K H L]

theorem lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.restr H = ⨆ χ : Weight K H L, I.restr H ⊓ genWeightSpace L χ := eq_iSup_inf_genWeightSpace (N := I.restr H)

