import Mathlib

variable {ι R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {s : Finset ι}

set_option linter.docPrime false in
theorem cast_finsetInf' (f : ι → ℕ) (hs) : (↑(s.inf' hs f) : R) = s.inf' hs fun i ↦ (f i : R) := comp_inf'_eq_inf'_comp _ _ cast_min

