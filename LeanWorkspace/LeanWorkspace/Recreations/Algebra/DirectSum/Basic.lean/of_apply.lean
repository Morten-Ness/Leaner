import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem of_apply {i : ι} (j : ι) (x : β i) : DirectSum.of β i x j = if h : i = j then Eq.recOn h x else 0 := DFinsupp.single_apply

