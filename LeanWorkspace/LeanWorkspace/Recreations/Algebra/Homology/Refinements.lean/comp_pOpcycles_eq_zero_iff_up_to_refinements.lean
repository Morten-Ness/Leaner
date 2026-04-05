import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)

theorem comp_pOpcycles_eq_zero_iff_up_to_refinements
      {A : C} {i : ι} (z : A ⟶ K.X i) (j : ι) (hj : c.prev i = j) :
      z ≫ K.pOpcycles i = 0 ↔
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ K.X j), π ≫ z = x ≫ K.d j i := by
  subst hj
  apply (K.sc i).comp_pOpcycles_eq_zero_iff_up_to_refinements

