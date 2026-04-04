import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem basisOf_apply (i : ι) (j : { j : ι // j ≠ i }) : b.basisOf i j = b ↑j -ᵥ b i := by
  simp [AffineBasis.basisOf]

