import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

variable [Fintype ι] [DecidableEq M]

theorem reindexFinsetRange_apply (x : Finset.univ.image b) : b.reindexFinsetRange x = x := by
  rcases x with ⟨bi, hbi⟩
  rcases Finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact Module.Basis.reindexFinsetRange_self b i

