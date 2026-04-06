FAIL
import Mathlib

variable {R : Type*} [CommRing R]

theorem quotient_iff_le_ker_natCast (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R) := by
  constructor
  · intro h
    intro m hm
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mp <| by
      exact CharP.cast_eq_zero_iff (R := R ⧸ I) n m |>.2 hm
  · intro h
    rw [charP_iff]
    intro m
    constructor
    · intro hm
      exact CharP.cast_eq_zero_iff (R := R ⧸ I) n m |>.2 hm
    · intro hm
      exact h <| Ideal.Quotient.eq_zero_iff_mem.mpr hm
