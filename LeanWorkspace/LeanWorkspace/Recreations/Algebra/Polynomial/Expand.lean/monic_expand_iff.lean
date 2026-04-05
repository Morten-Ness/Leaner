import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem monic_expand_iff {p : ℕ} {f : R[X]} (hp : 0 < p) : (Polynomial.expand R p f).Monic ↔ f.Monic := by
  simp only [Polynomial.Monic, Polynomial.leadingCoeff_expand hp]

alias ⟨_, Polynomial.Monic.expand⟩ := monic_expand_iff

