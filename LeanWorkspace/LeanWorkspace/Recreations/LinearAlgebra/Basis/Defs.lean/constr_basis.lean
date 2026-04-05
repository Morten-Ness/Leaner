import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

variable [Module R M']

variable (S : Type*) [Semiring S] [Module S M']

variable [SMulCommClass R S M']

theorem constr_basis (f : ι → M') (i : ι) : (Module.Basis.constr (M' := M') b S f : M → M') (b i) = f i := by
  simp [Module.Basis.constr_apply, Module.Basis.repr_self b]

