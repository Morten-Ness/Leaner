import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable (f : Π i, M i →ₗ[R] N i)

theorem lmap_eq_iff (x y : ⨁ i, M i) :
    DirectSum.lmap f x = DirectSum.lmap f y ↔ ∀ i, f i (x i) = f i (y i) := map_eq_iff (fun i => (f i).toAddMonoidHom) _ _

