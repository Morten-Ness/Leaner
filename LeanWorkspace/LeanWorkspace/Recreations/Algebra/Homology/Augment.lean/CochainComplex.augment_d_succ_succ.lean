import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augment_d_succ_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
    (i j : ℕ) : (CochainComplex.augment C f w).d (i + 1) (j + 1) = C.d i j := rfl

