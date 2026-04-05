import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

variable [Module R M']

variable (i : ι)

variable (e : ι ≃ ι')

variable (S : Type*) [Semiring S] [Module S M']

variable [SMulCommClass R S M']

theorem coord_equivFun_symm [Finite ι] (b : Module.Basis ι R M) (i : ι) (f : ι → R) :
    b.coord i (b.equivFun.symm f) = f i := Module.Basis.coord_repr_symm b i (Finsupp.equivFunOnFinite.symm f)

