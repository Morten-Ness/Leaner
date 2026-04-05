import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_val {a x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy (a : M) x y := congr_arg Units.val h

