import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_univ₀' [Fintype β] {s : Finset α} (hs : s.Nontrivial) : s • (univ : Finset β) = univ := coe_injective <| by push_cast; exact Set.smul_univ₀' hs

