import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply [DecidableEq ι] (i j : ι) : b.coord i (b j) = if i = j then 1 else 0 := by
  simpa using b.coord_apply i j
