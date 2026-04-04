import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

variable {ι' : Type*}

theorem affineIndependent_of_toMatrix_right_inv [Fintype ι] [Finite ι'] [DecidableEq ι']
    (p : ι' → P) {A : Matrix ι ι' k} (hA : b.toMatrix p * A = 1) : AffineIndependent k p := by
  cases nonempty_fintype ι'
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro w₁ w₂ hw₁ hw₂ hweq
  have hweq' : w₁ ᵥ* b.toMatrix p = w₂ ᵥ* b.toMatrix p := by
    ext j
    change (∑ i, w₁ i • b.coord j (p i)) = ∑ i, w₂ i • b.coord j (p i)
    rw [← Finset.univ.affineCombination_eq_linear_combination _ _ hw₁,
      ← Finset.univ.affineCombination_eq_linear_combination _ _ hw₂,
      ← Function.comp_def (b.coord j) p, ← Finset.univ.map_affineCombination p w₁ hw₁,
      ← Finset.univ.map_affineCombination p w₂ hw₂, hweq]
  replace hweq' := congr_arg (fun w => w ᵥ* A) hweq'
  simpa only [Matrix.vecMul_vecMul, hA, Matrix.vecMul_one] using hweq'

