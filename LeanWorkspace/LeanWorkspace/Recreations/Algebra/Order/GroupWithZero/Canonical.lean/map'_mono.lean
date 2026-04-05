import Mathlib

variable {α β : Type*}

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

theorem map'_mono [MulOneClass α] [MulOneClass β] {f : α →* β} (hf : Monotone f) :
    Monotone (map' f) := by simpa [Monotone, WithZero.forall]

