import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

theorem descOpcycles_comp {A A' : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) (α : A ⟶ A') :
    K.descOpcycles k j hj hk ≫ α = K.descOpcycles (k ≫ α) j hj
      (by rw [reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_descOpcycles_assoc, HomologicalComplex.p_descOpcycles]

