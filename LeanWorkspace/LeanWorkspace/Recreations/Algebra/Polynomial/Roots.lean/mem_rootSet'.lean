import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem mem_rootSet' {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S] {a : S} :
    a ∈ p.rootSet S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  classical
  rw [Polynomial.rootSet_def, Finset.mem_coe, mem_toFinset, Polynomial.mem_aroots']

