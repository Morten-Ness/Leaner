import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem affineCombination_affineCombinationSingleWeights [DecidableEq ι] (p : ι → P) {i : ι}
    (hi : i ∈ s) : s.affineCombination k p (Finset.affineCombinationSingleWeights k i) = p i := by
  refine Finset.affineCombination_of_eq_one_of_eq_zero s _ _ hi (by simp) ?_
  rintro j - hj
  simp [hj]

