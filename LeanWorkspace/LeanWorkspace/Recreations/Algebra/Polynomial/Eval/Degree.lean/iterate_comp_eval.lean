import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem iterate_comp_eval :
    ∀ (k : ℕ) (t : R), (p.comp^[k] q).eval t = (fun x => p.eval x)^[k] (q.eval t) := Polynomial.iterate_comp_eval₂ _

