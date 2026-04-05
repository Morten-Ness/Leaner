import Mathlib

variable {α : Type*}

variable [Zero α] [One α] [LE α] [ZeroLEOneClass α]

theorem mk_eq_one {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 1 ↔ x = 1 := Subtype.ext_iff

