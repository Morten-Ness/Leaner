import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem coe_monoidHom_comp_coe_monoidHom_symm (e : M ≃* N) :
    (e : M →* N).comp e.symm = MonoidHom.id _ := by ext; simp

