import Mathlib

variable {F R S : Type*}

theorem map_rat_algebraMap [Semiring R] [Semiring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S)
    (r : ℚ) : f (algebraMap ℚ R r) = algebraMap ℚ S r := RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r

