import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable [MulOneClass N]

theorem eqLocusM_same (f : M →* N) : f.eqLocusM f = ⊤ := SetLike.ext fun _ => eq_self_iff_true _

