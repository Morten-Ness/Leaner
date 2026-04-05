import Mathlib

variable {ι R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {s : Finset ι}

set_option linter.docPrime false in
theorem cast_finsetSup' (f : ι → ℕ) (hs) : ((s.sup' hs f : ℕ) : R) = s.sup' hs fun i ↦ (f i : R) := comp_sup'_eq_sup'_comp _ _ cast_max

