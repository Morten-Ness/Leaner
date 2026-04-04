import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (ι k) in

theorem mem_fintypeAffineCoords_iff_sum [Fintype ι] {w : ι → k} :
    w ∈ fintypeAffineCoords ι k ↔ ∑ i, w i = 1 := by
  simp [fintypeAffineCoords, Fintype.linearCombination_apply]

