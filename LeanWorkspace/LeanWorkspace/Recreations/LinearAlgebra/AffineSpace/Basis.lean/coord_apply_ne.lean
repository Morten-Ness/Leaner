import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply_ne (h : i ≠ j) : b.coord i (b j) = 0 := by
  rw [AffineBasis.coord, AffineMap.coe_mk, ← Subtype.coe_mk (p := (· ≠ i)) j h.symm, ← b.basisOf_apply,
    Basis.sumCoords_self_apply, sub_self]

