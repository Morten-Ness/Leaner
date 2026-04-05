import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem preimage_eval_singleton (hp : p ≠ C a) : p.eval ⁻¹' {a} = (p - C a).rootSet R := by
  ext; simp [Polynomial.mem_rootSet_of_ne (sub_ne_zero.mpr hp), sub_eq_zero]

