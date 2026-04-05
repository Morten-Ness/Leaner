import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem aeval_eq_aeval_mod_charpoly (M : Matrix n n R) (p : R[Polynomial.X]) :
    aeval M p = aeval M (p %ₘ M.charpoly) := (aeval_modByMonic_eq_self_of_root M.aeval_self_charpoly).symm

