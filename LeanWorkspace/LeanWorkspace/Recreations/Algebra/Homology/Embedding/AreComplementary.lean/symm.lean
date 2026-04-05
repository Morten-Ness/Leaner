import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

theorem symm : ComplexShape.Embedding.AreComplementary e₂ e₁ where
  disjoint i₂ i₁ := (ac.disjoint i₁ i₂).symm
  union i := (ac.union i).symm

