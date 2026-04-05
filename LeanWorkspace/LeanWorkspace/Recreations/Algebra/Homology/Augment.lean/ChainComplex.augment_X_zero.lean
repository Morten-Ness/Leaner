import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augment_X_zero (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (ChainComplex.augment C f w).X 0 = X := rfl

