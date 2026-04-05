import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem hom_ext' (φ : K ⟶ L) (hK : K.IsStrictlySupportedOutside e₂)
    (hL : L.IsStrictlySupportedOutside e₁) :
    φ = 0 := by
  ext i
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · apply (hL.isZero i₁).eq_of_tgt
  · apply (hK.isZero i₂).eq_of_src

