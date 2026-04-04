import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem affineCombinationSingleWeights_apply_self [DecidableEq ι] (i : ι) :
    Finset.affineCombinationSingleWeights k i i = 1 := Pi.single_eq_same _ _

