import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem induction_on' {motive : (⨁ i, β i) → Prop} (f : ⨁ i, β i) (h0 : motive 0)
    (hadd : ∀ (i b) (f : ⨁ i, β i), f i = 0 → b ≠ 0 → motive f → motive (DirectSum.of β i b + f)) :
    motive f := DFinsupp.induction f h0 hadd

