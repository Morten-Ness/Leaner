import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

theorem comp_liftCycles {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (α : A' ⟶ A) :
    α ≫ K.liftCycles k j hj hk = K.liftCycles (α ≫ k) j hj (by rw [assoc, hk, comp_zero]) := by
  simp only [← cancel_mono (K.iCycles i), assoc, HomologicalComplex.liftCycles_i]

