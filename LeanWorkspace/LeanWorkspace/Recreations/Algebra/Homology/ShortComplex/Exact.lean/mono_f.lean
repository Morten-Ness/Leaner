import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem mono_f (s : S.Splitting) : Mono S.f := by
  have := CategoryTheory.ShortComplex.Splitting.isSplitMono_f s
  infer_instance

