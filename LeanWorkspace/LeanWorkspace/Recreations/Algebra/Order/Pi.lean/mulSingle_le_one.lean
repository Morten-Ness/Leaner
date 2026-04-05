import Mathlib

variable {I α β γ : Type*}

variable {f : I → Type*}

variable {ι : Type*} {α : ι → Type*} [DecidableEq ι] [∀ i, One (α i)] [∀ i, Preorder (α i)] {i : ι}
  {a b : α i}

theorem mulSingle_le_one : mulSingle i a ≤ 1 ↔ a ≤ 1 := by simp [mulSingle]

