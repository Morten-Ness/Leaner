import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

variable (b' : Basis ι' R M')

variable (e : ι ≃ ι')

theorem coe_reindex : (b.reindex e : ι' → M) = b ∘ e.symm := funext (Module.Basis.reindex_apply b e)

