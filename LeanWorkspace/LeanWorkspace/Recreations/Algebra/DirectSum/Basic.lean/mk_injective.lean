import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem mk_injective (s : Finset ι) : Function.Injective (DirectSum.mk β s) := DFinsupp.mk_injective s

