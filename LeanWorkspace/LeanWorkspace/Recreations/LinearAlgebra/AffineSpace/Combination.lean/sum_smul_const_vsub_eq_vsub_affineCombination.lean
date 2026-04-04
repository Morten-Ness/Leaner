import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem sum_smul_const_vsub_eq_vsub_affineCombination (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = p₁ -ᵥ s.affineCombination k p₂ w := by
  rw [Finset.sum_smul_vsub_eq_affineCombination_vsub, Finset.affineCombination_apply_const _ _ _ h]

