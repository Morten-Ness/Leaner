import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm := MulEquiv.injective MulEquiv.symm_bijective <| MulEquiv.ext fun _ => rfl

