import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_univ₀' {s : Set α} (hs : s.Nontrivial) : s • (univ : Set β) = univ := Set.smul_univ₀ hs.not_subset_singleton

