import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_div_cancel (a b : G) : a / (a / b) = b := div_div_self' a b

