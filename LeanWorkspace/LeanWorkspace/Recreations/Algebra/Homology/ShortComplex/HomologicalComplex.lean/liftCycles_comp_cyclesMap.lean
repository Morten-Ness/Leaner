import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

variable [L.HasHomology i] [M.HasHomology i]

theorem liftCycles_comp_cyclesMap {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (φ : K ⟶ L) :
    K.liftCycles k j hj hk ≫ HomologicalComplex.cyclesMap φ i = L.liftCycles (k ≫ φ.f i) j hj
      (by rw [assoc, φ.comm, reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_mono (L.iCycles i), assoc, HomologicalComplex.cyclesMap_i, liftCycles_i_assoc, HomologicalComplex.liftCycles_i]

