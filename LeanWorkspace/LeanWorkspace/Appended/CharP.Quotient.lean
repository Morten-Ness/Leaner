import Mathlib

section

variable {R : Type*} [CommRing R]

theorem quotient_iff (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0 := by
  refine ⟨fun _ x hx => ?_, CharP.quotient' n I⟩
  rw [CharP.cast_eq_zero_iff R n, ← CharP.cast_eq_zero_iff (R ⧸ I) n _]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hx

end

section

variable {R : Type*} [CommRing R]

theorem quotient_iff_le_ker_natCast (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R) := by
  rw [CharP.quotient_iff, RingHom.ker_eq_comap_bot]; rfl

end
