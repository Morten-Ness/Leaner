import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R]

theorem ExpChar.eq {p q : ℕ} (hp : ExpChar R p) (hq : ExpChar R q) : p = q := by
  rcases hp with ⟨hp⟩ | ⟨hp'⟩
  · rcases hq with hq | hq'
    exacts [rfl, False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hq'))]
  · rcases hq with hq | hq'
    exacts [False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hp')),
      CharP.eq R ‹_› ‹_›]

