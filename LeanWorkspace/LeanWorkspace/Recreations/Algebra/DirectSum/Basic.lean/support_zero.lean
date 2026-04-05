import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem support_zero [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] : (0 : ⨁ i, β i).support = ∅ := DFinsupp.support_zero

