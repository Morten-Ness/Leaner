import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem isComplex_iff_of_iso {S₁ S₂ : CategoryTheory.ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.IsComplex ↔ S₂.IsComplex := ⟨CategoryTheory.ComposableArrows.isComplex_of_iso e, CategoryTheory.ComposableArrows.isComplex_of_iso e.symm⟩

