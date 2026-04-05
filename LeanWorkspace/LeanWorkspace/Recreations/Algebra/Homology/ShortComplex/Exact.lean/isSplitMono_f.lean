import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem isSplitMono_f (s : S.Splitting) : IsSplitMono S.f := ⟨⟨s.splitMono_f⟩⟩

