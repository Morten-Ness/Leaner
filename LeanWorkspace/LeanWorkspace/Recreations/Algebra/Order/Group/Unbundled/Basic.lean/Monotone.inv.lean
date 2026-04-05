import Mathlib

variable {α : Type u}

variable {β : Type*} [Group α] [Preorder α] [MulLeftMono α]
  [MulRightMono α] [Preorder β] {f : β → α} {s : Set β}

theorem Monotone.inv (hf : Monotone f) : Antitone fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

