import Mathlib

variable (R : Type*)

theorem charZero_iff_forall_prime_ne_zero [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ↔ ∀ p : ℕ, p.Prime → (p : R) ≠ 0 := by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h => have : CharP R 0 := h ▸ inferInstance; exact CharP.charP_to_charZero R

