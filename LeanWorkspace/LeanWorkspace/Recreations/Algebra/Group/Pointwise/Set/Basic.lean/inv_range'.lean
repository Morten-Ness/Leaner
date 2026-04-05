import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_range' {ι : Type*} {f : ι → α} : (range f)⁻¹ = range f⁻¹ := Set.inv_range

