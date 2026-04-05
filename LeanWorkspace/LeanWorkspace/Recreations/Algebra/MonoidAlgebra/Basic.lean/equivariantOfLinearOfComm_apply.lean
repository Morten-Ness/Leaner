import Mathlib

variable {R S T A B C M N O : Type*}

variable [Monoid M] [CommSemiring R] {V W : Type*} [AddCommMonoid V] [Module R V]
  [Module R[M] V] [IsScalarTower R R[M] V] [AddCommMonoid W]
  [Module R W] [Module R[M] W] [IsScalarTower R R[M] W]
  (f : V →ₗ[R] W)

variable (h : ∀ (g : M) (v : V), f (single g (1 : R) • v) = single g (1 : R) • f v)

theorem equivariantOfLinearOfComm_apply (v : V) : (MonoidAlgebra.equivariantOfLinearOfComm f h) v = f v := rfl

