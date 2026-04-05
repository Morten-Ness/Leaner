import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augmentTruncate_hom_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (ChainComplex.augmentTruncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1)) := rfl

