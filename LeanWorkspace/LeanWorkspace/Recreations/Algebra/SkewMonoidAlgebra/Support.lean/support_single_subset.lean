import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [AddCommMonoid k] {a : G} {b : k}

theorem support_single_subset : (single a b).support ⊆ {a} := Finsupp.support_single_subset

