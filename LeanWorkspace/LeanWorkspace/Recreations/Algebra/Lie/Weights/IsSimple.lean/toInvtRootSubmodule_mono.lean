import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem toInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I ≤ J) :
    I.toInvtRootSubmodule (H := H) ≤ J.toInvtRootSubmodule :=
  Submodule.span_mono (Set.image_mono
    fun α (hα : rootSpace H α.1 ≤ I.restr H) ↦ hα.trans (show I.restr H ≤ J.restr H from h))

