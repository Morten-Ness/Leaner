import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (b : Basis ι R M)

theorem singleton_apply (ι R : Type*) [Unique ι] [Semiring R] (i) : Module.Basis.singleton ι R i = 1 := apply_eq_iff.mpr (by simp [Module.Basis.singleton])

