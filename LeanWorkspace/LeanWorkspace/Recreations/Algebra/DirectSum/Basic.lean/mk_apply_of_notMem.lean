import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem mk_apply_of_notMem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∉ s) :
    DirectSum.mk β s f n = 0 := DFinsupp.mk_of_notMem hn

