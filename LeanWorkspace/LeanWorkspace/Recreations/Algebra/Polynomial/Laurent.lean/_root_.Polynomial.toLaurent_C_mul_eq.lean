import Mathlib

open scoped Polynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_C_mul_eq (r : R) (f : R[X]) :
    toLaurent (Polynomial.C r * f) = Polynomial.C r * toLaurent f := by
  simp only [map_mul, Polynomial.toLaurent_C]

