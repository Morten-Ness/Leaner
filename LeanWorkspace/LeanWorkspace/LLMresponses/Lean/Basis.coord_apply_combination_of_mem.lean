import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply_combination_of_mem (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = w i := by
  simpa using b.coord_apply_combination_of_mem hi hw
