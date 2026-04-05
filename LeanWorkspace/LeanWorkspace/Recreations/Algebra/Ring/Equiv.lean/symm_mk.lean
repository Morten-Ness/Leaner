import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) :
    (RingEquiv.mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm =
      { symm_mk.aux f g h₁ h₂ h₃ h₄ with
        toFun := g
        invFun := f } :=
  rfl

