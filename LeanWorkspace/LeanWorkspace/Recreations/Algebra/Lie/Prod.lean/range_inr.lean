import Mathlib

variable {R L₁ L₂ L L₃ L₄ L₅ L₆ : Type*}
  [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  [LieRing L] [LieAlgebra R L] [LieRing L₃] [LieAlgebra R L₃] [LieRing L₄] [LieAlgebra R L₄]
  [LieRing L₅] [LieAlgebra R L₅] [LieRing L₆] [LieAlgebra R L₆]

theorem range_inr : range (LieHom.inr R L₁ L₂) = ker (LieHom.fst R L₁ L₂) := by
  rw [← LieSubalgebra.toSubmodule_inj, range_toSubmodule, LieIdeal.toLieSubalgebra_toSubmodule,
   ker_toSubmodule]
  exact LinearMap.range_inr R L₁ L₂

