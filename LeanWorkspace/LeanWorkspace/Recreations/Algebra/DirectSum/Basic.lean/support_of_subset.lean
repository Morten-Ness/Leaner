import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem support_of_subset [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] {i : ι} {b : β i} :
    (DirectSum.of _ i b).support ⊆ {i} := DFinsupp.support_single_subset

