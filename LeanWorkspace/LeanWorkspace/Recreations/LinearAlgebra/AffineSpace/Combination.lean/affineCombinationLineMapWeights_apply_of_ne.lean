import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem affineCombinationLineMapWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t ≠ i)
    (hj : t ≠ j) (c : k) : Finset.affineCombinationLineMapWeights i j c t = 0 := by
  simp [Finset.affineCombinationLineMapWeights, hi, hj]

