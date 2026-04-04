import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem sum_smul_vsub_eq_affineCombination_vsub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) =
      s.affineCombination k p₁ w -ᵥ s.affineCombination k p₂ w := by
  simp_rw [Finset.affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

