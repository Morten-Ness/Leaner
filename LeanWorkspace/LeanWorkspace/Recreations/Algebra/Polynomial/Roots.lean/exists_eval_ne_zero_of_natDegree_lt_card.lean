import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem exists_eval_ne_zero_of_natDegree_lt_card (f : R[X]) (hf : f ≠ 0) (hfR : f.natDegree < #R) :
    ∃ r, f.eval r ≠ 0 := by
  contrapose! hf
  exact Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card f hf hfR

