import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem Parallel.trans {s₁ s₂ s₃ : AffineSubspace k P} (h₁₂ : s₁ ∥ s₂) (h₂₃ : s₂ ∥ s₃) :
    s₁ ∥ s₃ := by
  rcases h₁₂ with ⟨v₁₂, rfl⟩
  rcases h₂₃ with ⟨v₂₃, rfl⟩
  refine ⟨v₂₃ + v₁₂, ?_⟩
  rw [AffineSubspace.map_map, ← coe_trans_to_affineMap, ← constVAdd_add]

