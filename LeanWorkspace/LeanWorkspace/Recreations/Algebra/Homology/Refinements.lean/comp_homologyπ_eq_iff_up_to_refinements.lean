import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)

theorem comp_homologyπ_eq_iff_up_to_refinements
    (i j : ι) (hi : c.prev j = i)
    {A : C} (z₂ z₂' : A ⟶ K.cycles j) : z₂ ≫ K.homologyπ j = z₂' ≫ K.homologyπ j ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i),
        π ≫ z₂ = π ≫ z₂' + x₁ ≫ K.toCycles i j := by
  subst hi
  exact (K.sc j).comp_homologyπ_eq_iff_up_to_refinements z₂ z₂'

