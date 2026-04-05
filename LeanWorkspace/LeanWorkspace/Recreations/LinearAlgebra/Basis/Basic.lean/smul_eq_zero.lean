import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable (b : Basis ι R M)

theorem smul_eq_zero [IsDomain R] (b : Module.Basis ι R M) {c : R} {x : M} :
    c • x = 0 ↔ c = 0 ∨ x = 0 := by have := b.isTorsionFree; exact smul_eq_zero

