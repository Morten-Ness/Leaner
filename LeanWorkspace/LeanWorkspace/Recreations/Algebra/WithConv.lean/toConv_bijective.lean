import Mathlib

variable {R A B C : Type*}

theorem toConv_bijective : Function.Bijective (@toConv A) := ⟨WithConv.toConv_injective, WithConv.toConv_surjective⟩

