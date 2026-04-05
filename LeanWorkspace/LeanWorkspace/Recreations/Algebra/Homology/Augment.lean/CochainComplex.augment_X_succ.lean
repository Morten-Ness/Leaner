import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augment_X_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
    (i : ℕ) : (CochainComplex.augment C f w).X (i + 1) = C.X i := rfl

