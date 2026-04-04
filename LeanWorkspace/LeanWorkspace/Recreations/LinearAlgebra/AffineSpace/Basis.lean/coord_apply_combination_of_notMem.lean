import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply_combination_of_notMem (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = 0 := by
  classical simp only [AffineBasis.coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

