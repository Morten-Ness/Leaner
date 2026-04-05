import Mathlib

variable {α : Type*}

variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α]

theorem antitone_const_tsub : Antitone fun x => c - x := fun _ _ hxy => tsub_le_tsub rfl.le hxy

