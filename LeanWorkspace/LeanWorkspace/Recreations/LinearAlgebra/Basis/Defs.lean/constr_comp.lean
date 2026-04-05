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

theorem constr_comp (f : M' →ₗ[R] M') (v : ι → M') :
    Module.Basis.constr (M' := M') b S (f ∘ v) = f.comp (Module.Basis.constr (M' := M') b S v) :=
  Module.Basis.ext b fun i => by simp only [Module.Basis.constr_basis, LinearMap.comp_apply, Function.comp]

