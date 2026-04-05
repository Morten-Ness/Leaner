import Mathlib

variable {R : Type*} [CommRing R]

theorem quotient_iff (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0 := by
  refine ⟨fun _ x hx => ?_, CharP.quotient' n I⟩
  rw [CharP.cast_eq_zero_iff R n, ← CharP.cast_eq_zero_iff (R ⧸ I) n _]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hx

