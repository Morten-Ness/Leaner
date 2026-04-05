import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

variable (b' : Basis ι' R M')

variable (e : ι ≃ ι')

theorem repr_reindex_apply (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') := show (Finsupp.domLCongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp

