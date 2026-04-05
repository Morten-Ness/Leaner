import Mathlib

variable {R : Type*} [CommRing R]

theorem Ideal.natCast_mem_of_charP_quotient (p : ℕ) (I : Ideal R) [CharP (R ⧸ I) p] :
    (p : R) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp <| by simp

