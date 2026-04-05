import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_C_mul_X_pow [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (C a * X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [Polynomial.aroots_C_mul _ ha, Polynomial.aroots_X_pow]

