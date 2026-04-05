import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augment_d_zero_one (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (CochainComplex.augment C f w).d 0 1 = f := rfl

