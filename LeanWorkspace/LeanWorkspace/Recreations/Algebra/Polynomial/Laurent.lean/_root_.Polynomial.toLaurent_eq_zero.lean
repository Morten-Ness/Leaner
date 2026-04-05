import Mathlib

open scoped Polynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_eq_zero {f : R[X]} : toLaurent f = 0 ↔ f = 0 := map_eq_zero_iff _ Polynomial.toLaurent_injective

