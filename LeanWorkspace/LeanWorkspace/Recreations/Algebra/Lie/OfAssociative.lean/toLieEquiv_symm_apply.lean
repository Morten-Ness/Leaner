import Mathlib

variable {R : Type u} {A₁ : Type v} {A₂ : Type w}

variable [CommRing R] [Ring A₁] [Ring A₂] [Algebra R A₁] [Algebra R A₂]

variable (e : A₁ ≃ₐ[R] A₂)

theorem toLieEquiv_symm_apply (x : A₂) : e.toLieEquiv.symm x = e.symm x := rfl

