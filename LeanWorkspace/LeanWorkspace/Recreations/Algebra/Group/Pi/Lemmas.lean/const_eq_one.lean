import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [One α] [Nonempty ι] {a : α}

theorem const_eq_one : const ι a = 1 ↔ a = 1 := @const_inj _ _ _ _ 1

