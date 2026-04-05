import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [NonUnitalNonAssocSemiring α]

theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α) :
    A * B = of fun _ => ![] := funext fun _ => empty_eq _

