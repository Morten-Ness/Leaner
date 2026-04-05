import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

variable {p q : R[A]}

theorem ne_zero_of_not_supDegree_le {b : B} (h : ¬ p.supDegree D ≤ b) : p ≠ 0 := AddMonoidAlgebra.ne_zero_of_supDegree_ne_bot (fun he => h <| he ▸ bot_le)

