import Mathlib

variable {R : Type*} [CommRing R]

theorem vecMulSL {v : Fin 2 → R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) :
    IsCoprime ((v ᵥ* A.1) 0) ((v ᵥ* A.1) 1) := by
  obtain ⟨g, hg⟩ := IsCoprime.exists_SL2_row hab 0
  have : v = g 0 := funext fun t ↦ by { fin_cases t <;> tauto }
  simpa only [this] using Matrix.SpecialLinearGroup.isCoprime_row (g * A) 0

