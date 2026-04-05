import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [PerfectField K]

theorem lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
    {α : Weight K H L} {e f : L} (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α)) :
    ⁅e, f⁆ = killingForm K L e f • (LieAlgebra.IsKilling.cartanEquivDual H).symm α := by
  apply LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα
  exact LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace heα

