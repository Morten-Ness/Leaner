import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_list_prod (L : List R[X]) :
    (0 : R[X]) ∉ L → L.prod.roots = (L : Multiset R[X]).bind Polynomial.roots := List.recOn L (fun _ => Polynomial.roots_one) fun hd tl ih H => by
    rw [List.mem_cons, not_or] at H
    rw [List.prod_cons, Polynomial.roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2), ←
      Multiset.cons_coe, Multiset.cons_bind, ih H.2]

