import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem weightedVSub_vadd_affineCombination (w₁ w₂ : ι → k) (p : ι → P) :
    s.weightedVSub p w₁ +ᵥ s.affineCombination k p w₂ = s.affineCombination k p (w₁ + w₂) := by
  rw [← vadd_eq_add, AffineMap.map_vadd, Finset.affineCombination_linear]

