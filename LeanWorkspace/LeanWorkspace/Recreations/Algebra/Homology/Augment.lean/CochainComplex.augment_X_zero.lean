import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augment_X_zero (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (CochainComplex.augment C f w).X 0 = X := rfl

