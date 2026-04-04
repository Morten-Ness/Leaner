import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P]

variable (k V) {p₁ p₂ : P}

theorem coe_affineSpan_singleton (p : P) : (affineSpan k ({p} : Set P) : Set P) = {p} := by
  ext x
  rw [mem_coe, ← AffineSubspace.vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_singleton p)) _,
    direction_affineSpan]
  simp

