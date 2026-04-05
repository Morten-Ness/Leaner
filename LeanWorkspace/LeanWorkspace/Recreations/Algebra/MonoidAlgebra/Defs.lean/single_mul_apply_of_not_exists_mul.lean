import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

theorem single_mul_apply_of_not_exists_mul (r : R) (x : R[M]) (h : ¬ ∃ d, m' = m * d) :
    (single m r * x) m' = 0 := by classical simp_all [MonoidAlgebra.mul_apply, eq_comm]

