import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKProjective_iff_of_iso {K₁ K₂ : CochainComplex C ℤ} (e : K₁ ≅ K₂) :
    K₁.IsKProjective ↔ K₂.IsKProjective := ⟨fun _ ↦ CochainComplex.isKProjective_of_iso e, fun _ ↦ CochainComplex.isKProjective_of_iso e.symm⟩

