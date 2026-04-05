import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem coe_monoidHom_symm_comp_coe_monoidHom (e : M ≃* N) :
    (e.symm : N →* M).comp e = MonoidHom.id _ := by ext; simp

