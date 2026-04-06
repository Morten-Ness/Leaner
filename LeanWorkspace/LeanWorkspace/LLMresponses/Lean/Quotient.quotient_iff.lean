FAIL
import Mathlib

variable {R : Type*} [CommRing R]

theorem quotient_iff (n : ℕ) [CharZero R] (I : Ideal R) :
    CharZero (R ⧸ I) ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0 := by
  constructor
  · intro h x hx
    apply_mod_cast (show ((x : R) : R ⧸ I) = 0 by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  · intro h
    exact
      { cast_injective := by
          intro a b hab
          by_cases hmem : ((a - b : ℕ) : R) ∈ I
          · have hz : ((a - b : ℕ) : R) = 0 := h (a - b) hmem
            exact Nat.sub_eq_zero_of_le <| by
              simpa using_mod_cast hz
          · have hab' : (((a - b : ℕ) : R) : R ⧸ I) = 0 := by
              simpa using sub_eq_zero.mp hab
            exact False.elim <| hmem <| Ideal.Quotient.eq_zero_iff_mem.mp hab' }
