import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem of_eq_same (i : ι) (x : β i) : (DirectSum.of _ i x) i = x := DFinsupp.single_eq_same

