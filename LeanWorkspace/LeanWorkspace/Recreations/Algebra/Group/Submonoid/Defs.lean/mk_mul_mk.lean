import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
    (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ := rfl

