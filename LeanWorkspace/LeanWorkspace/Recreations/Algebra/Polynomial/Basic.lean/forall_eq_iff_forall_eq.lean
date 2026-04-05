import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem forall_eq_iff_forall_eq : (∀ f g : R[X], f = g) ↔ ∀ a b : R, a = b := by
  simpa only [← subsingleton_iff] using Polynomial.subsingleton_iff_subsingleton

