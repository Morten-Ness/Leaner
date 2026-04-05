import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_comp_C : toLaurent (R := R) ∘ Polynomial.C = Polynomial.C :=
  funext Polynomial.toLaurent_C

