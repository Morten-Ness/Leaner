import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable [MulOneClass N]

theorem eqLocusM_same (f : M →* N) : f.eqLocusM f = ⊤ := by
  ext x
  simp [MonoidHom.eqLocusM]
