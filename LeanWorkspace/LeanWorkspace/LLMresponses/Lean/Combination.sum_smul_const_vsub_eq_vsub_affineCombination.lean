FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem sum_smul_const_vsub_eq_vsub_affineCombination (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = p₁ -ᵥ s.affineCombination k p₂ w := by
  simpa using Finset.weightedVSub_eq_vsub_affineCombination (k := k) (s := s) (w := w) (p := p₂) (b := p₁) h
