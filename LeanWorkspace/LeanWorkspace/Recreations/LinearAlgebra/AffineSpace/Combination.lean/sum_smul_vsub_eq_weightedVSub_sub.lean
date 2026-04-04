import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_vsub_eq_weightedVSub_sub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) = s.weightedVSub p₁ w - s.weightedVSub p₂ w := s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

