import Mathlib

variable {R S : Type*}

variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

theorem div_neg_eq_neg_div' (a : R) : a / -b = -a / b := neg_div b a ▸ div_neg _

