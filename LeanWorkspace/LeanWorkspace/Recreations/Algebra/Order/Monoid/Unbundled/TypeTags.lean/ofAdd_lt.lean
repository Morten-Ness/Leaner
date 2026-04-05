import Mathlib

variable {α : Type*}

variable [Preorder α]

theorem ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b := Iff.rfl

