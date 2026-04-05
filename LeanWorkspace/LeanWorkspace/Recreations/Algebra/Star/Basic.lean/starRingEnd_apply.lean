import Mathlib

open scoped Ring

variable {R : Type u}

variable [CommSemiring R] [StarRing R]

theorem starRingEnd_apply (x : R) : starRingEnd R x = star x := rfl

-- Not `@[simp]` because `simp` can already prove it.

