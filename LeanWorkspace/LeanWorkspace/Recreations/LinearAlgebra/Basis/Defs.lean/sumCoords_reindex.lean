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

theorem sumCoords_reindex : (b.reindex e).sumCoords = b.sumCoords := by
  ext x
  simp only [Module.Basis.coe_sumCoords, Module.Basis.repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

