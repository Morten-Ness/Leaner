import Mathlib

variable {S M G : Type*}

theorem eq [Mul S] {a x y : S} (h : SemiconjBy a x y) : a * x = y * a := h

