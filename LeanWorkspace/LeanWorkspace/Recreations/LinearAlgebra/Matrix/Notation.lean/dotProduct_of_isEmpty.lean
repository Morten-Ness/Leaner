import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [AddCommMonoid α] [Mul α]

theorem dotProduct_of_isEmpty [Fintype n'] [IsEmpty n'] (v w : n' → α) : v ⬝ᵥ w = 0 := Finset.sum_of_isEmpty _

