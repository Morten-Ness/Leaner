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

theorem sumCoords_self_apply : b.sumCoords (b i) = 1 := by
  simp only [Module.Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id, Module.Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]

