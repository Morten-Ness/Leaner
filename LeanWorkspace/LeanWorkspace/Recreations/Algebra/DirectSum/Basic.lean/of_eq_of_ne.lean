import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem of_eq_of_ne (i j : ι) (x : β i) (h : j ≠ i) : (DirectSum.of _ i x) j = 0 := DFinsupp.single_eq_of_ne h

