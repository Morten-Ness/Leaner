FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem sum_smul_vsub_const_eq_affineCombination_vsub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.affineCombination k p₁ w -ᵥ p₂ := by
  classical
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (s := s) (k := k)
      (p₁ := p₁) (w := w) h]
  simp [Finset.weightedVSubOfPoint_apply]
