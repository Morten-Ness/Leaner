import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [AddCommMonoid k] {a : G} {b : k}

theorem support_single_ne_zero (a : G) (h : b ≠ 0) : (single a b).support = {a} := Finsupp.support_single_ne_zero _ h

