import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem isSupportedOutside₂_iff :
    K.IsSupportedOutside e₂ ↔ K.IsSupported e₁ := ComplexShape.Embedding.AreComplementary.isSupportedOutside₁_iff ComplexShape.Embedding.AreComplementary.symm ac K

