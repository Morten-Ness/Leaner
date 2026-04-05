import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem isRoot_comp {R} [CommSemiring R] {p q : R[X]} {r : R} :
    (p.comp q).IsRoot r ↔ p.IsRoot (q.eval r) := by simp_rw [Polynomial.IsRoot, Polynomial.eval_comp]

