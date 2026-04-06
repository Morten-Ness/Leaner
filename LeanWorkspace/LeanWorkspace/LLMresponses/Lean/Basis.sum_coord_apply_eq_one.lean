import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem sum_coord_apply_eq_one [Fintype ι] (q : P) : ∑ i, b.coord i q = 1 := by
  simpa using b.sum_coord q
