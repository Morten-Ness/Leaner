import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)

theorem liftCycles_comp_homologyπ_eq_iff_up_to_refinements
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    {A : C} (x₂ x₂' : A ⟶ K.X j) (hx₂ : x₂ ≫ K.d j k = 0) (hx₂' : x₂' ≫ K.d j k = 0) :
    K.liftCycles x₂ k hk hx₂ ≫ K.homologyπ j = K.liftCycles x₂' k hk hx₂' ≫ K.homologyπ j ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ K.X i), π ≫ x₂ = π ≫ x₂' + x₁ ≫ K.d i j := by
  subst hi hk
  exact (K.sc j).liftCycles_comp_homologyπ_eq_iff_up_to_refinements x₂ x₂' hx₂ hx₂'

