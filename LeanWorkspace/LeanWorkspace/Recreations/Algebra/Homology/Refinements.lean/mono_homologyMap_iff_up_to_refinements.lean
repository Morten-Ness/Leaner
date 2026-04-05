import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)

theorem mono_homologyMap_iff_up_to_refinements
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Mono (homologyMap φ j) ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ K.X j) (_ : x₂ ≫ K.d j k = 0) (y₁ : A ⟶ L.X i)
          (_ : x₂ ≫ φ.f j = y₁ ≫ L.d i j),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i),
          π ≫ x₂ = x₁ ≫ K.d i j := by
  subst hi hk
  apply ShortComplex.mono_homologyMap_iff_up_to_refinements

