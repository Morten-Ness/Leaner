import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem augmentTruncate_hom_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (CochainComplex.augmentTruncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1)) := rfl

