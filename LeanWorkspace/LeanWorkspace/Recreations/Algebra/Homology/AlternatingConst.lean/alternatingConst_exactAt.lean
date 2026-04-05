import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] [HasZeroObject C]

theorem alternatingConst_exactAt (X : C) (n : ℕ) (hn : n ≠ 0) :
    (ChainComplex.alternatingConst.obj X).ExactAt n := by
  rcases n.even_or_odd with h | h
  · exact ⟨(ChainComplex.alternatingConstHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(ChainComplex.alternatingConstHomologyDataOdd X _ h), isZero_zero C⟩

