import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem mk_apply_of_mem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∈ s) :
    DirectSum.mk β s f n = f ⟨n, hn⟩ := DFinsupp.mk_of_mem hn

