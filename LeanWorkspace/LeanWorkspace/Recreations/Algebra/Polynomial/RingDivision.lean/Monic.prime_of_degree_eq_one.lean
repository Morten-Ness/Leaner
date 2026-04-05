import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Polynomial.Monic p) : Prime p := have : p = Polynomial.X - Polynomial.C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ Polynomial.prime_X_sub_C _

