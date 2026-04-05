import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem card_roots (hp0 : p ≠ 0) : (Multiset.card (Polynomial.roots p) : WithBot ℕ) ≤ degree p := by
  classical
  unfold Polynomial.roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1

