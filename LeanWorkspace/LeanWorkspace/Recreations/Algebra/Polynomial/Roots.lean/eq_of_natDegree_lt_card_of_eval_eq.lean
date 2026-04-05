import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem eq_of_natDegree_lt_card_of_eval_eq {R} [CommRing R] [IsDomain R]
    (p q : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i : ι, eval (f i) p = eval (f i) q)
    (hcard : max p.natDegree q.natDegree < Fintype.card ι) : p = q := by
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  · simpa [sub_eq_zero]
  · grind [natDegree_sub_le]

