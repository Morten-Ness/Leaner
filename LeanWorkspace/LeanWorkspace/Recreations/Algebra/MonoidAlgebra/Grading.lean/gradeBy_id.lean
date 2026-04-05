import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable (R) [CommSemiring R]

theorem gradeBy_id : gradeBy R (id : M → M) = grade R := rfl

