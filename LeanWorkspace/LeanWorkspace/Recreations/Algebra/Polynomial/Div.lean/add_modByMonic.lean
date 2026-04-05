import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (Polynomial.div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add, add_left_comm, add_assoc, Polynomial.modByMonic_add_div, ← add_assoc,
              add_comm (q * _), Polynomial.modByMonic_add_div],
            (degree_add_le _ _).trans_lt
              (max_lt (Polynomial.degree_modByMonic_lt _ hq) (Polynomial.degree_modByMonic_lt _ hq))⟩).2
  · simp_rw [Polynomial.modByMonic_eq_of_not_monic _ hq]

