import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

theorem Basis.ofEquivFun_equivFun [Finite ι] (v : Basis ι R M) :
    Module.Basis.ofEquivFun v.equivFun = v := Basis.repr_injective <| by ext; rfl

