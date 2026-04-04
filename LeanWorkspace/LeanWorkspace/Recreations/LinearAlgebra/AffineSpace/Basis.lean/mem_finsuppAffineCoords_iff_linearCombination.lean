import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (ι k) in

theorem mem_finsuppAffineCoords_iff_linearCombination {w : ι →₀ k} :
    w ∈ finsuppAffineCoords ι k ↔ Finsupp.linearCombination k (1 : ι → k) w = 1 := by
  simp [finsuppAffineCoords]

