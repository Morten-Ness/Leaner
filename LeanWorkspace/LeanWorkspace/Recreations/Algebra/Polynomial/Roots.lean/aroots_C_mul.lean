import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_C_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (C a * p).aroots S = p.aroots S := by
  rw [Polynomial.aroots_def, Polynomial.map_mul, map_C, Polynomial.roots_C_mul]
  rwa [map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

