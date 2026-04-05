import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {R} [CommRing R] [IsDomain R]
    (p : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = 0) (hcard : natDegree p < #s) :
    p = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

