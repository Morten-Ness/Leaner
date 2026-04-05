import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem sum_support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (x : ⨁ i, β i) :
    (∑ i ∈ x.support, DirectSum.of β i (x i)) = x := DFinsupp.sum_single

