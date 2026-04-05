import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem LeftHomologyData.leftHomologyIso_hom_comp_homologyIso_inv (h : S.LeftHomologyData) :
    h.leftHomologyIso.hom ≫ h.homologyIso.inv = S.leftHomologyIso.hom := by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

