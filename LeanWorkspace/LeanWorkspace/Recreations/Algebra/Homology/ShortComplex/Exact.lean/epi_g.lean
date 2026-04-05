import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem epi_g (s : S.Splitting) : Epi S.g := by
  have := CategoryTheory.ShortComplex.Splitting.isSplitEpi_g s
  infer_instance

