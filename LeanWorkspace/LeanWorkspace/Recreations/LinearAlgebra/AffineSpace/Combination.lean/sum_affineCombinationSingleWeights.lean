import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem sum_affineCombinationSingleWeights [DecidableEq ι] {i : ι} (h : i ∈ s) :
    ∑ j ∈ s, Finset.affineCombinationSingleWeights k i j = 1 := by
  rw [← Finset.affineCombinationSingleWeights_apply_self k i]
  exact sum_eq_single_of_mem i h fun j _ hj => Finset.affineCombinationSingleWeights_apply_of_ne k hj

