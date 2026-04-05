import Mathlib

variable {α β : Type*}

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

theorem map'_strictMono [MulOneClass α] [MulOneClass β] {f : α →* β} (hf : StrictMono f) :
    StrictMono (map' f) := by simpa [StrictMono, WithZero.forall]

