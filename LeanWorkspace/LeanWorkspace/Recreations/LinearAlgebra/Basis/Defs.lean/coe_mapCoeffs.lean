import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

variable {R' : Type*} [Semiring R'] [Module R' M] (f : R ≃+* R')

variable (h : ∀ (c) (x : M), f c • x = c • x)

theorem coe_mapCoeffs : (b.mapCoeffs f h : ι → M) = b := funext <| Module.Basis.mapCoeffs_apply b f h

