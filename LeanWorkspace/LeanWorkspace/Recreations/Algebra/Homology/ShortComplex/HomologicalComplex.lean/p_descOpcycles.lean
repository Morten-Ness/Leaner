import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

set_option backward.isDefEq.respectTransparency false in
theorem p_descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpcycles k j hj hk = k := by
  dsimp [HomologicalComplex.descOpcycles, HomologicalComplex.pOpcycles]
  simp

