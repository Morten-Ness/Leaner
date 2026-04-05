import Mathlib

variable {G M R K : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

theorem exists_pow_lt {a : G} (ha : a < 1) (b : G) : ∃ n : ℕ, a ^ n < b := (exists_lt_pow (one_lt_inv'.mpr ha) b⁻¹).imp <| by simp

