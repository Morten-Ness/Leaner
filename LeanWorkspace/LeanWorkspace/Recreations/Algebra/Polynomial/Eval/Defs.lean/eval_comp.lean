import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval_comp : (p.comp q).eval x = p.eval (q.eval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [Polynomial.add_comp, hr, hs]
  | monomial n a => simp

