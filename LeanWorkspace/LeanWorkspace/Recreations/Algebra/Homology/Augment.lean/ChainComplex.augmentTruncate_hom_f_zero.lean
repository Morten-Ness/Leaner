import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augmentTruncate_hom_f_zero (C : ChainComplex V ℕ) :
    (ChainComplex.augmentTruncate C).hom.f 0 = 𝟙 (C.X 0) := rfl

