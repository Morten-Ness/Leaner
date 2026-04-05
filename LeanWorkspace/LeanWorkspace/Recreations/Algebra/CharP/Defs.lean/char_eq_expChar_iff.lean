import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R]

theorem char_eq_expChar_iff (p q : ℕ) [hp : CharP R p] [hq : ExpChar R q] : p = q ↔ p.Prime := by
  rcases hq with q | hq_prime
  · rw [(CharP.eq R hp (.ofCharZero R) : p = 0)]
    decide
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp ‹CharP R q›⟩

