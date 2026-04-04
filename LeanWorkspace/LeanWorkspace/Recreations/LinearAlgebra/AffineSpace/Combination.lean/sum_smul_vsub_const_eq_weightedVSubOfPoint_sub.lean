import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_vsub_const_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ : ι → P) (p₂ b : P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSubOfPoint p₁ b w - (∑ i ∈ s, w i) • (p₂ -ᵥ b) := by
  rw [Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub, Finset.weightedVSubOfPoint_apply_const]

