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

variable {M'' : Type*} (b' : Basis ι' R M') (e : ι ≃ ι')

variable [AddCommMonoid M''] [Module R M'']

variable {R M M' : Type*} [CommSemiring R]

variable (b : Basis ι R M) (b' : Basis ι' R M')

variable [SMulCommClass R R M']

theorem equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
    (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) := Module.Basis.constr_basis b' R _ _

