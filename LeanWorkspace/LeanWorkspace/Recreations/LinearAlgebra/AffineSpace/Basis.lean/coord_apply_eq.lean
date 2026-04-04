import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply_eq (i : ι) : b.coord i (b i) = 1 := by
  simp only [AffineBasis.coord, Basis.coe_sumCoords, map_zero, sub_zero,
    AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]

