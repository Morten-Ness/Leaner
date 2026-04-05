import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact_iff_of_iso {S₁ S₂ : CategoryTheory.ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.Exact ↔ S₂.Exact := ⟨CategoryTheory.ComposableArrows.exact_of_iso e, CategoryTheory.ComposableArrows.exact_of_iso e.symm⟩

