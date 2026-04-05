import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem snd_inj {i₁ : ι₁} {i₂ i₂' : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁ i₂') :
    i₂ = i₂' := e₂.injective_f (c.next_eq h h')

