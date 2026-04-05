import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem of_boundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ac.Boundary i₁ (ComplexShape.Embedding.AreComplementary.Boundary.indexOfBoundaryLE ac h) := (ComplexShape.Embedding.AreComplementary.Boundary.exists₁ ac h).choose_spec

