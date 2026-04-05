import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ↔ S₂.Exact := ⟨CategoryTheory.ShortComplex.exact_of_iso e, CategoryTheory.ShortComplex.exact_of_iso e.symm⟩

