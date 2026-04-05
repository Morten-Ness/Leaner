import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.mono_g' (hS : S.Exact) (h : RightHomologyData S) : Mono h.g' := mono_of_isZero_kernel' _ h.hι (by
    haveI := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

