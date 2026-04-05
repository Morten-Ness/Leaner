import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [CommGroup G] {s t : Set G} {a : G}

theorem smul_set_stabilizer_subset (ha : a ∈ s) : a • (stabilizer G s : Set G) ⊆ s := by
  simpa using MulAction.op_smul_set_stabilizer_subset ha

