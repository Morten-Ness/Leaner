import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem affineCombinationSingleWeights_apply_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) :
    Finset.affineCombinationSingleWeights k i j = 0 := Pi.single_eq_of_ne h _

