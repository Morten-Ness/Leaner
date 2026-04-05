import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]

theorem isoHomologyι_hom_inv_id :
    K.homologyι i ≫ (K.isoHomologyι i j hj h).inv = 𝟙 _ := (K.isoHomologyι i j hj h).hom_inv_id

