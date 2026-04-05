import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

theorem mk_mul_mk (x y : M) (hx : x ∈ S') (hy : y ∈ S') :
    (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, Subsemigroup.mul_mem hx hy⟩ := rfl

