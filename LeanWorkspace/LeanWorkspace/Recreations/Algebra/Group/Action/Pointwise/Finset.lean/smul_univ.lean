import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_univ [Fintype β] {s : Finset α} (hs : s.Nonempty) : s • (univ : Finset β) = univ := coe_injective <| by
    push_cast
    exact Set.smul_univ hs

