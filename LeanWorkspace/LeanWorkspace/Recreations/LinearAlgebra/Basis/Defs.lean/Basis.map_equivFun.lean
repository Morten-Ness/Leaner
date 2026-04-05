import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

theorem Basis.map_equivFun [Finite ι] (b : Basis ι R M) (f : M ≃ₗ[R] M') :
    (b.map f).equivFun = f.symm.trans b.equivFun := rfl

