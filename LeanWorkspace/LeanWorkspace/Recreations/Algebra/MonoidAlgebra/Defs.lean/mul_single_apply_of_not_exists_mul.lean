import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

theorem mul_single_apply_of_not_exists_mul (r : R) (x : R[M]) (h : ¬ ∃ d, m' = d * m) :
    (x * single m r) m' = 0 := by classical simp_all [MonoidAlgebra.mul_apply, eq_comm]

