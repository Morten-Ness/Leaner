import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem isComplex_of_iso {S₁ S₂ : CategoryTheory.ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) :
    S₂.IsComplex where
  zero i hi := by
    rw [← cancel_epi (CategoryTheory.ComposableArrows.app' e.hom i), comp_zero,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality,
      reassoc_of% (h₁.zero i hi), zero_comp]

