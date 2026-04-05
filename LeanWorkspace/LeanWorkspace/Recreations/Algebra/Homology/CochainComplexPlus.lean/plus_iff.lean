import Mathlib

variable (C : Type*) [Category* C]

theorem plus_iff [HasZeroMorphisms C] (K : CochainComplex C ℤ) :
    CochainComplex.plus C K ↔ ∃ (n : ℤ), K.IsStrictlyGE n := Iff.rfl

