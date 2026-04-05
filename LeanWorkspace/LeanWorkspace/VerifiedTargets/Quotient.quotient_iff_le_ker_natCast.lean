import Mathlib

variable {R : Type*} [CommRing R]

theorem quotient_iff_le_ker_natCast (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R) := by
  rw [CharP.quotient_iff, RingHom.ker_eq_comap_bot]; rfl

