import Mathlib

variable {G : Type*}

variable {α : Type*} (P : Prop) [Decidable P]

variable [Div α]

theorem div_ite (a b c : α) : (a / if P then b else c) = if P then a / b else a / c := div_dite ..

