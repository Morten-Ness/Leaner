import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m → m.prod.roots = m.bind Polynomial.roots := by
  rcases m with ⟨L⟩
  simpa only [Multiset.prod_coe, quot_mk_to_coe''] using Polynomial.roots_list_prod L

