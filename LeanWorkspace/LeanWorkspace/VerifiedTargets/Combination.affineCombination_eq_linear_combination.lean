import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_eq_linear_combination (s : Finset ι) (p : ι → V) (w : ι → k)
    (hw : ∑ i ∈ s, w i = 1) : s.affineCombination k p w = ∑ i ∈ s, w i • p i := by
  simp [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one s w p hw 0]

