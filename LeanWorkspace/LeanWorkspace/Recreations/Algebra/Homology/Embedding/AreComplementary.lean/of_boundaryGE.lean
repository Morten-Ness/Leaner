import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem of_boundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ac.Boundary (ComplexShape.Embedding.AreComplementary.Boundary.indexOfBoundaryGE ac h) i₂ := (ComplexShape.Embedding.AreComplementary.Boundary.exists₂ ac h).choose_spec

