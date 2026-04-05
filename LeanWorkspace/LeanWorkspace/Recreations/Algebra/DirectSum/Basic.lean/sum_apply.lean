import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem sum_apply {α} (s : Finset α) (g : α → ⨁ i, β i) (i : ι) :
    (∑ a ∈ s, g a) i = ∑ a ∈ s, g a i := DFinsupp.finset_sum_apply s g i

