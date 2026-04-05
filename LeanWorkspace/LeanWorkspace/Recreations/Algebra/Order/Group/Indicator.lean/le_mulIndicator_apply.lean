import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [LE M] [One M] {s : Set α} {f g : α → M} {a : α} {y : M}

theorem le_mulIndicator_apply (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) :
    y ≤ mulIndicator s g a := Set.mulIndicator_apply_le' (M := Mᵒᵈ) hfg hf

