import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem _root_.Matrix.mem_range_scalar_iff_commute_transvectionStruct {M : Matrix n n R} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ t : Matrix.TransvectionStruct n R, Commute t.toMatrix M := by
  refine ⟨fun h t => ?_, mem_range_scalar_of_commute_transvectionStruct⟩
  rw [mem_range_scalar_iff_commute_single] at h
  refine (Commute.one_left M).add_left ?_
  convert (h _ _ t.hij).smul_left t.c using 1
  rw [smul_single, smul_eq_mul, mul_one]

