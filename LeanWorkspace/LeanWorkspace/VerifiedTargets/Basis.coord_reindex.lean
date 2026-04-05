import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_reindex (i : ι') : (b.reindex e).coord i = b.coord (e.symm i) := by
  ext
  classical simp [AffineBasis.coord]

