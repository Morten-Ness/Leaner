import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem natDegree_pos_of_monic_of_aeval_eq_zero [Nontrivial R] [Semiring S] [Algebra R S]
    [FaithfulSMul R S] {p : R[X]} (hp : p.Monic) {x : S} (hx : Polynomial.aeval x p = 0) :
    0 < p.natDegree := Polynomial.natDegree_pos_of_aeval_root (Polynomial.Monic.ne_zero hp) hx
    ((injective_iff_map_eq_zero (algebraMap R S)).mp (FaithfulSMul.algebraMap_injective R S))

