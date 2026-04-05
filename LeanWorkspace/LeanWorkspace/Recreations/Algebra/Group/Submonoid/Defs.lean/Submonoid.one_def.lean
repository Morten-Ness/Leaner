import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ := rfl

