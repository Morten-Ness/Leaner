import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem isRoot_prod {R} [CommSemiring R] [IsDomain R] {ι : Type*} (s : Finset ι) (p : ι → R[X])
    (x : R) : Polynomial.IsRoot (∏ j ∈ s, p j) x ↔ ∃ i ∈ s, Polynomial.IsRoot (p i) x := by
  simp only [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff]

