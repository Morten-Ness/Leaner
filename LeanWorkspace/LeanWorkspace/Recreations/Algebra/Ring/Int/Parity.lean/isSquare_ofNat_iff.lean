import Mathlib

variable {m n : ℤ}

theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (ofNat(n) : ℤ) ↔ IsSquare (ofNat(n) : ℕ) := Int.isSquare_natCast_iff

-- These next two don't make good `norm_cast` lemmas.

