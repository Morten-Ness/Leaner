import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem isPrimePow_iff_pow_succ : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ p ^ (k + 1) = n := (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨p, k - 1, hp, by rwa [Nat.sub_add_cancel hk]⟩, fun ⟨_, _, hp, hn⟩ =>
      ⟨_, _, hp, Nat.succ_pos', hn⟩⟩

