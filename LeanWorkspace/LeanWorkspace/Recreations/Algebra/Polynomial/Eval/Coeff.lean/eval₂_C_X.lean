import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

theorem eval₂_C_X : eval₂ Polynomial.C Polynomial.X p = p := Polynomial.induction_on' p (fun p q hp hq => by simp [hp, hq]) fun n x => by
    rw [eval₂_monomial, ← smul_X_eq_monomial, C_mul']

