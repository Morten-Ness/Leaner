import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u := Units.ext hv

