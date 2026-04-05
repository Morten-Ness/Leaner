import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]

theorem isoHomologyπ_inv_hom_id :
    (K.isoHomologyπ i j hi h).inv ≫ K.homologyπ j = 𝟙 _ := (K.isoHomologyπ i j hi h).inv_hom_id

