import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable (a b) [Semiring R]

theorem finrank_eq_two [StrongRankCondition R] :
    Module.finrank R (QuadraticAlgebra R a b) = 2 := by
  simp [Module.finrank, QuadraticAlgebra.rank_eq_two]

