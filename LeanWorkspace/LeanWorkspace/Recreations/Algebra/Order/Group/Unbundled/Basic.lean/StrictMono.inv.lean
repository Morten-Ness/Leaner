import Mathlib

variable {α : Type u}

variable {β : Type*} [Group α] [Preorder α] [MulLeftStrictMono α]
  [MulRightStrictMono α] [Preorder β] {f : β → α} {s : Set β}

theorem StrictMono.inv (hf : StrictMono f) : StrictAnti fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

