import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

variable {p q : R[A]}

theorem ne_zero_of_supDegree_ne_bot : p.supDegree D ≠ ⊥ → p ≠ 0 := mt (fun h => h ▸ AddMonoidAlgebra.supDegree_zero)

