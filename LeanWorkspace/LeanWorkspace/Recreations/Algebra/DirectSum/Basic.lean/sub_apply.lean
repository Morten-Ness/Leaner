import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommGroup (β i)]

theorem sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i := rfl

