import Mathlib

variable {C : Type*} [Category* C]

variable [Abelian C] (K L : CochainComplex C ℤ)

variable (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

theorem g_shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE n₀).g ≫ K.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h = K.πTruncGE n₁ := by
  apply HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE

