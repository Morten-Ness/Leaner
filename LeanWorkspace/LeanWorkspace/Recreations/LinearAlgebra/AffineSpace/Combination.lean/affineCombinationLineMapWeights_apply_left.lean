import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem affineCombinationLineMapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i ≠ j) (c : k) :
    Finset.affineCombinationLineMapWeights i j c i = 1 - c := by
  simp [Finset.affineCombinationLineMapWeights, h.symm, sub_eq_neg_add]

