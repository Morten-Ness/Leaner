import Mathlib

variable {α : Type*}

variable [Lattice α] [AddCommGroup α] {s t : Set α}

theorem solidClosure_min (hst : s ⊆ t) (ht : LatticeOrderedAddCommGroup.IsSolid t) : LatticeOrderedAddCommGroup.solidClosure s ⊆ t := fun _ ⟨_, hy, hxy⟩ ↦ ht (hst hy) hxy

