import Mathlib

variable {R A : Type*}

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

theorem charP_of_isFractionRing [CharP R p] : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective R K) p

