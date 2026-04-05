import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem modByMonic_eq_of_dvd_sub (hq : q.Monic) (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %ₘ q := by
  nontriviality R
  obtain ⟨f, sub_eq⟩ := h
  refine (Polynomial.div_modByMonic_unique (p₂ /ₘ q + f) _ hq ⟨?_, Polynomial.degree_modByMonic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_add, ← add_assoc, Polynomial.modByMonic_add_div, add_comm]

