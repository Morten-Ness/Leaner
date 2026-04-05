import Mathlib

variable {α : Type*}

variable [Lattice α] [AddCommGroup α] {s t : Set α}

theorem isSolid_solidClosure (s : Set α) : LatticeOrderedAddCommGroup.IsSolid (LatticeOrderedAddCommGroup.solidClosure s) := fun _ ⟨y, hy, hxy⟩ _ hzx ↦ ⟨y, hy, hzx.trans hxy⟩

