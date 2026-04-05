import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [NonUnitalNonAssocSemiring α]

theorem empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α) : A * B = of ![] := empty_eq _

