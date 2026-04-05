import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

theorem Basis.coe_ofEquivFun [Finite ι] [DecidableEq ι] (e : M ≃ₗ[R] ι → R) :
    (Module.Basis.ofEquivFun e : ι → M) = fun i => e.symm (Pi.single i 1) := funext fun i =>
    Module.Basis.injective e <|
      funext fun j => by
        simp [Module.Basis.ofEquivFun, ← Finsupp.single_eq_pi_single]

