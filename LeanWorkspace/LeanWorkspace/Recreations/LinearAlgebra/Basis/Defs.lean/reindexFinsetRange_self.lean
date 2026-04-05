import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

variable [Fintype ι] [DecidableEq M]

theorem reindexFinsetRange_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange ⟨b i, h⟩ = b i := by
  rw [Module.Basis.reindexFinsetRange, Module.Basis.reindex_apply, Module.Basis.reindexRange_apply]
  rfl

