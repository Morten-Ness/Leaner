import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem RightHomologyData.homologyIso_hom_comp_ι (h : S.RightHomologyData) :
    h.homologyIso.hom ≫ h.ι = S.homologyι ≫ h.opcyclesIso.hom := by
  dsimp only [CategoryTheory.ShortComplex.homologyι, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, rightHomologyIso_hom_comp_ι]

