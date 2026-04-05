import Mathlib

open scoped TensorProduct

variable (R A L : Type*)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

theorem toFinsupp_symm_single (c : A) (z : L) :
    (LieAlgebra.LoopAlgebra.toFinsupp R A L).symm (Finsupp.single c z) = AddMonoidAlgebra.single c 1 ⊗ₜ[R] z := by
  simp [LieAlgebra.LoopAlgebra.toFinsupp]

