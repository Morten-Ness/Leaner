import Mathlib

variable {ι R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {s : Finset ι}

theorem cast_finsetSup [OrderBot R] [CanonicallyOrderedAdd R] (s : Finset ι) (f : ι → ℕ) :
    (↑(s.sup f) : R) = s.sup fun i ↦ (f i : R) := comp_sup_eq_sup_comp _ cast_max (by simp)

