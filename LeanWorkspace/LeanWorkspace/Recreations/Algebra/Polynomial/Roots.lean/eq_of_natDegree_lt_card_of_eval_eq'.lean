import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem eq_of_natDegree_lt_card_of_eval_eq' {R} [CommRing R] [IsDomain R]
    (p q : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = q.eval i)
    (hcard : max p.natDegree q.natDegree < #s) : p = q := Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

