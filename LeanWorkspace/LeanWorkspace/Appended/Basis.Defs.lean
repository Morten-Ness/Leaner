import Mathlib

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

theorem Basis.equivFun_ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R) :
    (Module.Basis.ofEquivFun e).equivFun = e := by
  ext j
  simp_rw [Module.Basis.equivFun_apply, Module.Basis.ofEquivFun_repr_apply]

end
