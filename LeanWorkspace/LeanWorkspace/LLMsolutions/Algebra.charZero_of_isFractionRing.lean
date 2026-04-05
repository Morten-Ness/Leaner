FAIL
import Mathlib

variable {R A : Type*}

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

theorem charZero_of_isFractionRing [CharZero R] : CharZero K := by
  infer_instance
