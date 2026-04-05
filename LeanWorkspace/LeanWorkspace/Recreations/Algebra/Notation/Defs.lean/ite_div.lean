import Mathlib

variable {G : Type*}

variable {α : Type*} (P : Prop) [Decidable P]

variable [Div α]

theorem ite_div (a b c : α) : (if P then a else b) / c = if P then a / c else b / c := dite_div ..

