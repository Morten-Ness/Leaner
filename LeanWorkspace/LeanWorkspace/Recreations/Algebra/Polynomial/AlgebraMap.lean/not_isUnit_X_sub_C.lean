import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [Ring R]

theorem not_isUnit_X_sub_C [Nontrivial R] (r : R) : ¬IsUnit (Polynomial.X - Polynomial.C r) := fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ => zero_ne_one' R <| by rw [← Polynomial.eval_mul_X_sub_C, hgf, eval_one]

