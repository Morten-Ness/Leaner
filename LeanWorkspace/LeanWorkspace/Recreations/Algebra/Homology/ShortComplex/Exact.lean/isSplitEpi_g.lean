import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem isSplitEpi_g (s : S.Splitting) : IsSplitEpi S.g := ⟨⟨s.splitEpi_g⟩⟩

