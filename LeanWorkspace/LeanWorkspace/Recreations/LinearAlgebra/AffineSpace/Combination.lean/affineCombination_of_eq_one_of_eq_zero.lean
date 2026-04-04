import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_of_eq_one_of_eq_zero (w : ι → k) (p : ι → P) {i : ι} (his : i ∈ s)
    (hwi : w i = 1) (hw0 : ∀ i2 ∈ s, i2 ≠ i → w i2 = 0) : s.affineCombination k p w = p i := by
  have h1 : ∑ i ∈ s, w i = 1 := hwi ▸ sum_eq_single i hw0 fun h => False.elim (h his)
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h1 (p i),
    Finset.weightedVSubOfPoint_apply]
  convert zero_vadd V (p i)
  refine sum_eq_zero ?_
  intro i2 hi2
  by_cases h : i2 = i
  · simp [h]
  · simp [hw0 i2 hi2 h]

