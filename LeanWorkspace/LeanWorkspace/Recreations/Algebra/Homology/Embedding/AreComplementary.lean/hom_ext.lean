import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem hom_ext [K.IsStrictlySupported e₁] [L.IsStrictlySupported e₂] (φ : K ⟶ L) :
    φ = 0 := by
  apply ComplexShape.Embedding.AreComplementary.hom_ext' ac
  · rw [ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₂_iff ac]
    infer_instance
  · rw [ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₁_iff ac]
    infer_instance

