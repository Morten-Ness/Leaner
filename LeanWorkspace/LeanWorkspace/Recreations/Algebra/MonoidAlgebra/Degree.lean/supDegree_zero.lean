import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

variable {p q : R[A]}

set_option backward.isDefEq.respectTransparency false in
theorem supDegree_zero : (0 : R[A]).supDegree D = ⊥ := by simp [supDegree]

