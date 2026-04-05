import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

theorem iterate_apply_lie' (D : LieDerivation R L L) (n : ℕ) (a b : L) :
    D^[n] ⁅a, b⁆ = ∑ i ∈ range (n + 1), n.choose i • ⁅D^[i] a, D^[n - i] b⁆ := by
  rw [LieDerivation.iterate_apply_lie D n a b]
  exact sum_antidiagonal_eq_sum_range_succ (fun i j ↦ n.choose i • ⁅D^[i] a, D^[j] b⁆) n

