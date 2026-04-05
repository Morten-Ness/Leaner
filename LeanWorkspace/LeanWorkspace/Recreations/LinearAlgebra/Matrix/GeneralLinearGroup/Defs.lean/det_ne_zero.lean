import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

theorem det_ne_zero [Nontrivial R] (g : GL n R) : g.val.det ≠ 0 := g.det.ne_zero

