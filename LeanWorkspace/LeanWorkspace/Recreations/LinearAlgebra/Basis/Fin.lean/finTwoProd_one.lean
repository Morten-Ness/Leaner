import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

theorem finTwoProd_one (R : Type*) [Semiring R] : Module.Basis.finTwoProd R 1 = (0, 1) := by
  simp [Module.Basis.finTwoProd, LinearEquiv.finTwoArrow]

