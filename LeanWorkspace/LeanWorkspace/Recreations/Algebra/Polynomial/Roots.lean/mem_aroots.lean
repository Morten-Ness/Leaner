import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem mem_aroots [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a ∈ p.aroots S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [Polynomial.mem_aroots', Polynomial.map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

