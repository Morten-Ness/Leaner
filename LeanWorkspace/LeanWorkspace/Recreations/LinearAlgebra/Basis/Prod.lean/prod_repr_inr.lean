import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable (b' : Basis ι' R M')

theorem prod_repr_inr (x) (i) : (b.prod b').repr x (Sum.inr i) = b'.repr x.2 i := rfl

