import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem resolvent_eq {a : A} {r : R} (h : r ∈ resolventSet R a) : resolvent a r = ↑h.unit⁻¹ := Ring.inverse_unit h.unit

