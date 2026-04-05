import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem fromOpcycles_d :
    K.fromOpcycles i j ≫ K.d j k = 0 := by
  simp only [← cancel_epi (K.pOpcycles i), p_fromOpcycles_assoc, d_comp_d, comp_zero]

