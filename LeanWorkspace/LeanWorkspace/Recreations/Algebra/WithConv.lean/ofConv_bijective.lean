import Mathlib

variable {R A B C : Type*}

theorem ofConv_bijective : Function.Bijective (@ofConv A) := ⟨WithConv.ofConv_injective, WithConv.ofConv_surjective⟩

