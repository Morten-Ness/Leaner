import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)

theorem exactAt_iff_exact_up_to_refinements (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    K.ExactAt j ↔ ∀ ⦃A : C⦄ (x₂ : A ⟶ K.X j) (_ : x₂ ≫ K.d j k = 0),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i), π ≫ x₂ = x₁ ≫ K.d i j := by
  rw [K.exactAt_iff' i j k hi hk]
  exact (K.sc' i j k).exact_iff_exact_up_to_refinements

