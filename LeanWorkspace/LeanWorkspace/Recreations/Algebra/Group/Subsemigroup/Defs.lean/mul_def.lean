import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

theorem mul_def (x y : S') : x * y = ⟨x * y, Subsemigroup.mul_mem x.2 y.2⟩ := rfl

