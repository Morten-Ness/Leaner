import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable (f : Π i, M i →ₗ[R] N i)

theorem lmap_eq_map (x : ⨁ i, M i) : DirectSum.lmap f x = map (fun i => (f i).toAddMonoidHom) x := rfl

