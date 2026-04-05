import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : R[X]) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  refine Polynomial.induction_on φ ?_ ?_ ?_ <;>
    · intros
      simp_all only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, pow_succ, ← mul_assoc]

