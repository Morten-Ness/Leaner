import Mathlib

variable {α : Type u}

variable {β : Type*} [Group α] [Preorder α] [MulLeftStrictMono α]
  [MulRightStrictMono α] [Preorder β] {f : β → α} {s : Set β}

theorem StrictMonoOn.inv (hf : StrictMonoOn f s) : StrictAntiOn (fun x => (f x)⁻¹) s := fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

