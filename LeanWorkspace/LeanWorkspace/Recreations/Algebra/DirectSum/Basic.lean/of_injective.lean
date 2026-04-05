import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem of_injective (i : ι) : Function.Injective (DirectSum.of β i) := DFinsupp.single_injective

