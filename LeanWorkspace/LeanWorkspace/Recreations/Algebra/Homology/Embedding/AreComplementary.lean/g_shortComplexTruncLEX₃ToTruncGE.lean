import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex C c) {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c}
  [e₁.IsTruncLE] [e₂.IsTruncGE] (ac : e₁.AreComplementary e₂)

theorem g_shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE e₁).g ≫ K.shortComplexTruncLEX₃ToTruncGE ac = K.πTruncGE e₂ := cokernel.π_desc _ _ _

