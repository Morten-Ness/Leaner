import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

theorem repr_self_apply (j) [Decidable (i = j)] : b.repr (b i) j = if i = j then 1 else 0 := by
  rw [Module.Basis.repr_self, Finsupp.single_apply]

