import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

theorem repr_symm_apply (v) : b.repr.symm v = Finsupp.linearCombination R b v := calc
    b.repr.symm v = b.repr.symm (v.sum Finsupp.single) := by simp
    _ = v.sum fun i vi => b.repr.symm (Finsupp.single i vi) := map_finsuppSum ..
    _ = Finsupp.linearCombination R b v := by simp only [Module.Basis.repr_symm_single,
                                                         Finsupp.linearCombination_apply]

