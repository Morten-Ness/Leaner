import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (b : Basis ι R M)

theorem singleton_repr (ι R : Type*) [Unique ι] [Semiring R] (x i) :
    (Module.Basis.singleton ι R).repr x i = x := by simp [Module.Basis.singleton, Unique.eq_default i]

