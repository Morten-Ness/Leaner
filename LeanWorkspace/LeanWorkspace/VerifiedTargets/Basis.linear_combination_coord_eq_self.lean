import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem linear_combination_coord_eq_self [Fintype ι] (b : AffineBasis ι k V) (v : V) :
    ∑ i, b.coord i v • b i = v := by
  have hb := AffineBasis.affineCombination_coord_eq_self b v
  rwa [Finset.univ.affineCombination_eq_linear_combination _ _ (AffineBasis.sum_coord_apply_eq_one b v)] at hb

