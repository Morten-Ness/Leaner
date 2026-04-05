import Mathlib

theorem LieAlgebra.toModule_injective (L : Type*) [LieRing L] :
    Function.Injective (@LieAlgebra.toModule _ _ _ _ : LieAlgebra ℚ L → Module ℚ L) := by
  rintro ⟨h₁⟩ ⟨h₂⟩ heq
  congr

