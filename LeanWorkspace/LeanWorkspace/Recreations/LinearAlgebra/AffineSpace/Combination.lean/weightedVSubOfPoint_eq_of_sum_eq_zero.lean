import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_eq_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : ∑ i ∈ s, w i = 0)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w = s.weightedVSubOfPoint p b₂ w := by
  apply eq_of_sub_eq_zero
  rw [Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply, ← sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · ext
      rw [← smul_sub, vsub_sub_vsub_cancel_left]
  rw [← sum_smul, h, zero_smul]

