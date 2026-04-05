import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] [Semiring T] (f : R →+* S) (g : S →+* T) (p)

theorem hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) := by
  rw [← Polynomial.eval₂_map, eval₂_at_apply, Polynomial.eval_map]

