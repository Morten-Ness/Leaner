import Mathlib

open scoped TensorProduct

variable (R A L : Type*)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

theorem toFinsupp_single_tmul (c : A) (z : L) :
    (LieAlgebra.LoopAlgebra.toFinsupp R A L (AddMonoidAlgebra.single c 1 ⊗ₜ[R] z)) = Finsupp.single c z := by
  simp [← LieAlgebra.LoopAlgebra.toFinsupp_symm_single]

