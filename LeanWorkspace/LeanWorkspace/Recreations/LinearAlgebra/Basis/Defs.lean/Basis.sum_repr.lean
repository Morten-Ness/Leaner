import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

theorem Basis.sum_repr [Fintype ι] (b : Basis ι R M) (u : M) : ∑ i, b.repr u i • b i = u := b.sum_equivFun u

