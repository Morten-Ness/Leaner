import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

theorem reindexRange_self (i : ι) (h := Set.mem_range_self i) : b.reindexRange ⟨b i, h⟩ = b i := by
  cases subsingleton_or_nontrivial R
  · let := Module.subsingleton R M
    simp [Module.Basis.reindexRange, eq_iff_true_of_subsingleton]
  · simp [*, Module.Basis.reindexRange, Module.Basis.reindex_apply]

