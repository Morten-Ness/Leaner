import Mathlib

variable {α : Type u}

variable {β : Type*} [Group α] [Preorder α] [MulLeftMono α]
  [MulRightMono α] [Preorder β] {f : β → α} {s : Set β}

theorem AntitoneOn.inv (hf : AntitoneOn f s) : MonotoneOn (fun x => (f x)⁻¹) s := fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

