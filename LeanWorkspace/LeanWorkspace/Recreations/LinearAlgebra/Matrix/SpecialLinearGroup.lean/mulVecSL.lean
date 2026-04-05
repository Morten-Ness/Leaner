import Mathlib

variable {R : Type*} [CommRing R]

theorem mulVecSL {v : Fin 2 → R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) :
    IsCoprime ((A.1 *ᵥ v) 0) ((A.1 *ᵥ v) 1) := by
  simpa only [← vecMul_transpose] using IsCoprime.vecMulSL hab A.transpose

