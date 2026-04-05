import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

theorem repr_linearCombination (v) : b.repr (Finsupp.linearCombination _ b v) = v := by
  rw [← Module.Basis.coe_repr_symm b]
  exact b.repr.apply_symm_apply v

