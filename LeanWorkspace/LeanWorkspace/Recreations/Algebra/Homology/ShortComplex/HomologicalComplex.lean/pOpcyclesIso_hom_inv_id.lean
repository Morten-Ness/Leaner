import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]

theorem pOpcyclesIso_hom_inv_id :
    K.pOpcycles j ≫ (K.pOpcyclesIso i j hi h).inv = 𝟙 _ := (K.pOpcyclesIso i j hi h).hom_inv_id

