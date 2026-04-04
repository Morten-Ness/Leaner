import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

variable {ι' : Type*}

variable [Fintype ι] (b₂ : AffineBasis ι k P)

theorem toMatrix_vecMul_coords (x : P) : b₂.coords x ᵥ* b.toMatrix b₂ = b.coords x := by
  ext j
  change _ = b.coord j x
  conv_rhs => rw [← b₂.affineCombination_coord_eq_self x]
  rw [Finset.map_affineCombination _ _ _ (b₂.sum_coord_apply_eq_one x)]
  simp [Matrix.vecMul, dotProduct, AffineBasis.toMatrix_apply, coords]

