import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem comp_right_injective (e : M ≃* N) : Function.Injective fun f : P →* M ↦ (e : M →* N).comp f := LeftInverse.injective (g := (e.symm : N →* M).comp) fun f ↦ by simp [← MonoidHom.comp_assoc]

