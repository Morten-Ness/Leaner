import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_const_vsub_eq_neg_weightedVSub (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 0) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = -s.weightedVSub p₂ w := by
  rw [Finset.sum_smul_vsub_eq_weightedVSub_sub, Finset.weightedVSub_apply_const s _ _ h, zero_sub]

