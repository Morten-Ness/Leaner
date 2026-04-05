import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem isStrictlySupportedOutside₂_iff :
    K.IsStrictlySupportedOutside e₂ ↔ K.IsStrictlySupported e₁ := ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₁_iff ComplexShape.Embedding.AreComplementary.symm ac K

