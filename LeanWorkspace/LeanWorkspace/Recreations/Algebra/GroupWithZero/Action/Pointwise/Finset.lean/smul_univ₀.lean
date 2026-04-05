import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_univ₀ [Fintype β] {s : Finset α} (hs : ¬s ⊆ 0) : s • (univ : Finset β) = univ := coe_injective <| by
    rw [← coe_subset] at hs
    push_cast at hs ⊢
    exact Set.smul_univ₀ hs

