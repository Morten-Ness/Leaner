import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

theorem homologyι_descOpcycles_eq_zero_of_boundary {A : C} (k : K.X i ⟶ A) (j : ι)
    (hj : c.prev i = j) {i' : ι} (x : K.X i' ⟶ A) (hx : k = K.d i i' ≫ x) :
    K.homologyι i ≫ K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
  by_cases h : c.Rel i i'
  · obtain rfl := c.next_eq' h
    exact (K.sc i).homologyι_descOpcycles_eq_zero_of_boundary _ x hx
  · have : K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
      rw [K.shape _ _ h, zero_comp] at hx
      rw [← cancel_epi (K.pOpcycles i), comp_zero, HomologicalComplex.p_descOpcycles, hx]
    rw [this, comp_zero]

