import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_of_val {a x y : Mˣ} (h : SemiconjBy (a : M) x y) : SemiconjBy a x y := Units.ext h

