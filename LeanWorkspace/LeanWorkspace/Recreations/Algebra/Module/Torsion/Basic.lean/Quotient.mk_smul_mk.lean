import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

variable (M I) (s : Set R) (r : R)

theorem Quotient.mk_smul_mk [I.IsTwoSided] (r : R) (m : M) :
    Ideal.Quotient.mk I r •
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) m =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) (r • m) :=
  rfl

