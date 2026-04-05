import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

variable [ExpChar R p]

theorem expand_contract' [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0) :
    Polynomial.expand R p (Polynomial.contract p f) = f := by
  obtain _ | @⟨_, hprime, hchar⟩ := ‹ExpChar R p›
  · rw [Polynomial.expand_one, Polynomial.contract_one]
  · haveI := Fact.mk hchar; exact Polynomial.expand_contract p hf hprime.ne_zero

