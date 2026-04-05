import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem mul_divByMonic_eq_iff_isRoot : (Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a)) = p ↔ IsRoot p a := .trans
    ⟨fun h => by rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    fun h => by
      conv_rhs => rw [← Polynomial.modByMonic_add_div p, Polynomial.modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
    IsRoot.def.symm

