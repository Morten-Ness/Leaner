import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem RightHomologyData.homologyIso_hom_comp_rightHomologyIso_inv (h : S.RightHomologyData) :
    h.homologyIso.hom ≫ h.rightHomologyIso.inv = S.rightHomologyIso.inv := by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

