import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem weightedVSubVSubWeights_apply_left [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    Finset.weightedVSubVSubWeights k i j i = 1 := by simp [Finset.weightedVSubVSubWeights, h]

