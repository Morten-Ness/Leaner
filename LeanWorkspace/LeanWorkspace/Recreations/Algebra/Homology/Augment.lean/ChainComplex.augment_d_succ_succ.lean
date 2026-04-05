import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augment_d_succ_succ (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i j : ℕ) : (ChainComplex.augment C f w).d (i + 1) (j + 1) = C.d i j := by
  cases i <;> rfl

