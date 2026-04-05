import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ := rfl

