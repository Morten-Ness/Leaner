import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem eval₂_modByMonic_eq_self_of_root [CommRing S] {f : R →+* S} {p q : R[X]}
    {x : S} (hx : q.eval₂ f x = 0) : (p %ₘ q).eval₂ f x = p.eval₂ f x := by
  rw [Polynomial.modByMonic_eq_sub_mul_div, eval₂_sub, eval₂_mul, hx, zero_mul, sub_zero]

