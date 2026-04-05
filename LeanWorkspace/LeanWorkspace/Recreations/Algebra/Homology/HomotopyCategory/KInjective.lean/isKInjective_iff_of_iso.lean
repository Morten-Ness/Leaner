import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKInjective_iff_of_iso {L₁ L₂ : CochainComplex C ℤ} (e : L₁ ≅ L₂) :
    L₁.IsKInjective ↔ L₂.IsKInjective := ⟨fun _ ↦ CochainComplex.isKInjective_of_iso e, fun _ ↦ CochainComplex.isKInjective_of_iso e.symm⟩

