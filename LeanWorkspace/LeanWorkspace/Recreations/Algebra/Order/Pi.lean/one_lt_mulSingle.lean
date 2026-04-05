import Mathlib

variable {I α β γ : Type*}

variable {f : I → Type*}

variable {ι : Type*} {α : ι → Type*} [DecidableEq ι] [∀ i, One (α i)] [∀ i, Preorder (α i)] {i : ι}
  {a b : α i}

theorem one_lt_mulSingle : 1 < mulSingle i a ↔ 1 < a := by simp [mulSingle]

