import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable (a b) [Semiring R]

theorem rank_eq_two [StrongRankCondition R] : Module.rank R (QuadraticAlgebra R a b) = 2 := by
  simp [rank_eq_card_basis (QuadraticAlgebra.basis a b)]

