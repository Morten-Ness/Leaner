import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_vsub_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ p₂ : ι → P) (b : P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) =
      s.weightedVSubOfPoint p₁ b w - s.weightedVSubOfPoint p₂ b w := by
  simp_rw [Finset.weightedVSubOfPoint_apply, ← sum_sub_distrib, ← smul_sub, vsub_sub_vsub_cancel_right]

