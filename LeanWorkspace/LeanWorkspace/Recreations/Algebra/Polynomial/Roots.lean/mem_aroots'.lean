import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem mem_aroots' [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {a : S} :
    a ∈ p.aroots S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  rw [Polynomial.mem_roots', IsRoot.def, ← eval₂_eq_eval_map, aeval_def]

