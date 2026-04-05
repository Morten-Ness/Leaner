import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem RightHomologyData.rightHomologyIso_hom_comp_homologyIso_inv (h : S.RightHomologyData) :
    h.rightHomologyIso.hom ≫ h.homologyIso.inv = S.rightHomologyIso.hom := by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

