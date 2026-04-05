import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

variable (b' : Basis ι' R M')

variable (e : ι ≃ ι')

theorem reindex_refl : b.reindex (Equiv.refl ι) = b := by
  simp [Module.Basis.reindex]

