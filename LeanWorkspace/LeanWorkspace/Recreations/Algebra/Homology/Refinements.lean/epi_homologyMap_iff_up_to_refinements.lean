import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)

theorem epi_homologyMap_iff_up_to_refinements
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Epi (homologyMap φ j) ↔
      ∀ ⦃A : C⦄ (y₂ : A ⟶ L.X j) (_ : y₂ ≫ L.d j k = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ K.X j) (_ : x₂ ≫ K.d j k = 0)
          (y₁ : A' ⟶ L.X i), π ≫ y₂ = x₂ ≫ φ.f j + y₁ ≫ L.d i j := by
  subst hi hk
  apply ShortComplex.epi_homologyMap_iff_up_to_refinements

