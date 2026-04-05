import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem iterate_comp_eval₂ (k : ℕ) (t : S) :
    eval₂ f t (p.comp^[k] q) = (fun x => eval₂ f x p)^[k] (eval₂ f t q) := by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Polynomial.eval₂_comp, IH]

