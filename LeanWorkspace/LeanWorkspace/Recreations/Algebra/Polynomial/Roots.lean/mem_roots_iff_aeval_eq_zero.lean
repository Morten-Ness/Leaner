import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mem_roots_iff_aeval_eq_zero {x : R} (w : p ≠ 0) : x ∈ Polynomial.roots p ↔ aeval x p = 0 := by
  rw [aeval_def, ← Polynomial.mem_roots_map_of_injective (FaithfulSMul.algebraMap_injective _ _) w,
    Algebra.algebraMap_self, map_id]

