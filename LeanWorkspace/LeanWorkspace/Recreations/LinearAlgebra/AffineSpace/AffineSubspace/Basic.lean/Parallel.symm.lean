import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem Parallel.symm {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) : s₂ ∥ s₁ := by
  rcases h with ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  rw [AffineSubspace.map_map, ← coe_trans_to_affineMap, ← constVAdd_add, neg_add_cancel, constVAdd_zero,
    coe_refl_to_affineMap, AffineSubspace.map_id]

