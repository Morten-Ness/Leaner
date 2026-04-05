import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem comp_left_injective (e : M ≃* N) : Function.Injective fun f : N →* P ↦ f.comp (e : M →* N) := LeftInverse.injective (g := fun f ↦ f.comp e.symm) fun f ↦ by simp [MonoidHom.comp_assoc]

