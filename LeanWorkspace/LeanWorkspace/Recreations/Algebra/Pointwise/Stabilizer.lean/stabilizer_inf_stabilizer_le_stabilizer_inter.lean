import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem stabilizer_inf_stabilizer_le_stabilizer_inter :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∩ t) := MulAction.stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_inter

