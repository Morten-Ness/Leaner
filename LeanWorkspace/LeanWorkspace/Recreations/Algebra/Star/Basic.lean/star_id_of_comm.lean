import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_id_of_comm {R : Type*} [CommMonoid R] {x : R} : star x = x := rfl

