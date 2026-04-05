import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

theorem exists_supDegree_mem_support (hp : p ≠ 0) : ∃ a ∈ p.support, p.supDegree D = D a := Finset.exists_mem_eq_sup _ (Finsupp.support_nonempty_iff.mpr hp) D

