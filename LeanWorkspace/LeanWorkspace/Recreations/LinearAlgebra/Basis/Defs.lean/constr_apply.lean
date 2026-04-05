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

theorem constr_apply (f : ι → M') (x : M) :
    Module.Basis.constr (M' := M') b S f x = (b.repr x).sum fun b a => a • f b := by
  simp only [Module.Basis.constr_def, LinearMap.comp_apply, lmapDomain_apply, linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]

