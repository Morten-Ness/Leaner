import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact [HasZeroObject C] (s : S.Splitting) : S.Exact := ⟨s.homologyData, isZero_zero _⟩

