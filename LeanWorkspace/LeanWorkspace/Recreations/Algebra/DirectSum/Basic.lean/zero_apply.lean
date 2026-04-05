import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0 := rfl

