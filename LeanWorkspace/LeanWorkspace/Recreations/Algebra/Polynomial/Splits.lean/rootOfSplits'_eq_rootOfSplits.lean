import Mathlib

open scoped Polynomial

variable {R : Type*}

variable {F : Type u} {K : Type v} {L : Type w}

variable [CommRing R] [Field K] [Field L] [Field F]

variable (i : K →+* L)

theorem rootOfSplits'_eq_rootOfSplits {f : K[X]} (hf : (f.map i).Splits) (hfd) :
    Polynomial.rootOfSplits hf hfd = Polynomial.rootOfSplits hf (f.degree_map i ▸ hfd) := rfl

