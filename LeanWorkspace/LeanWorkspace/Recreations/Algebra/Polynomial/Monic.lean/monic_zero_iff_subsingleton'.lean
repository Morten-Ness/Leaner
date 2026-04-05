import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem monic_zero_iff_subsingleton' :
    Polynomial.Monic (0 : R[X]) ↔ (∀ f g : R[X], f = g) ∧ ∀ a b : R, a = b := Polynomial.monic_zero_iff_subsingleton.trans
    ⟨by
      intro
      simp [eq_iff_true_of_subsingleton], fun h => subsingleton_iff.mpr h.2⟩

