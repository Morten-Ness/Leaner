import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKProjective_of_iso {K₁ K₂ : CochainComplex C ℤ} (e : K₁ ≅ K₂)
    [K₁.IsKProjective] :
    K₂.IsKProjective := (HomotopyEquiv.ofIso e).isKProjective

