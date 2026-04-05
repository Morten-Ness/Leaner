import Mathlib

variable {G : Type*}

variable {α : Type*} (P : Prop) [Decidable P]

variable [Div α]

theorem ite_div_ite (a b c d : α) :
    ((if P then a else b) / if P then c else d) = if P then a / c else b / d := dite_div_dite ..

