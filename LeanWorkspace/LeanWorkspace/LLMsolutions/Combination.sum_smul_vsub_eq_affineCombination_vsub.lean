FAIL
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
  simpa [Finset.affineCombination] using
    (Finset.centerMass_vsub (s := s) (k := k) (t₁ := p₁) (t₂ := p₂) (w := w))
