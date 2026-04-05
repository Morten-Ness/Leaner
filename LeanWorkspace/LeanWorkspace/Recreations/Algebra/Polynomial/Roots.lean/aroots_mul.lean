import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q ≠ 0) :
    (p * q).aroots S = p.aroots S + q.aroots S := by
  suffices map (algebraMap T S) p * map (algebraMap T S) q ≠ 0 by
    rw [Polynomial.aroots_def, Polynomial.map_mul, Polynomial.roots_mul this]
  rwa [← Polynomial.map_mul, Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective T S)]

