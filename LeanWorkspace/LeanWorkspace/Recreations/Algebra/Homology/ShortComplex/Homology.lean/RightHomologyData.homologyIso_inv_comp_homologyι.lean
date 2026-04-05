import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem RightHomologyData.homologyIso_inv_comp_homologyι (h : S.RightHomologyData) :
    h.homologyIso.inv ≫ S.homologyι = h.ι ≫ h.opcyclesIso.inv := by
  dsimp only [CategoryTheory.ShortComplex.homologyι, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, assoc, Iso.hom_inv_id_assoc,
    rightHomologyIso_inv_comp_rightHomologyι]

