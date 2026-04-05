import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augmentTruncate_inv_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (CochainComplex.augmentTruncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) := rfl

