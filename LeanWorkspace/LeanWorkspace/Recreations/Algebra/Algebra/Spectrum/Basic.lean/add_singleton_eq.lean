import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem add_singleton_eq (a : A) (r : R) : σ a + {r} = σ (a + ↑ₐ r) := add_comm {r} (σ a) ▸ add_comm (algebraMap R A r) a ▸ spectrum.singleton_add_eq a r

