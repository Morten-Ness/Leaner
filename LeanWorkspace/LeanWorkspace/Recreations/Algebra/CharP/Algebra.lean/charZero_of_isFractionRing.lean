import Mathlib

variable {R A : Type*}

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

theorem charZero_of_isFractionRing [CharZero R] : CharZero K := @CharP.charP_to_charZero K _ (IsFractionRing.charP_of_isFractionRing R 0)

