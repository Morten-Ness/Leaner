import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]

theorem iCyclesIso_inv_hom_id :
    (K.iCyclesIso i j hj h).inv ≫ K.iCycles i = 𝟙 _ := (K.iCyclesIso i j hj h).inv_hom_id

