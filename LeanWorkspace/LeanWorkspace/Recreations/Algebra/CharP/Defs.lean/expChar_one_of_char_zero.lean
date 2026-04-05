import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R]

theorem expChar_one_of_char_zero (q : ℕ) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by
  rcases hq with q | hq_prime
  · rfl
  · exact False.elim <| hq_prime.ne_zero <| ‹CharP R q›.eq R hp

