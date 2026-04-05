import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]

variable {modM : Module ℤ M} {modM₂ : Module ℤ M₂} {modM₃ : Module ℤ M₃} (e : M ≃+ M₂)

theorem coe_toIntLinearEquiv : ⇑(e.toIntLinearEquiv (modM := modM) (modM₂ := modM₂)) = e := rfl

