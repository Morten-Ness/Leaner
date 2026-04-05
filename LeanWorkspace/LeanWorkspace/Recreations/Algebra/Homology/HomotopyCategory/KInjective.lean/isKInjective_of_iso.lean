import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKInjective_of_iso {L₁ L₂ : CochainComplex C ℤ} (e : L₁ ≅ L₂)
    [L₁.IsKInjective] :
    L₂.IsKInjective := (HomotopyEquiv.ofIso e).isKInjective

