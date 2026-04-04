import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_apply (w : ι → k) (p : ι → P) :
    (s.affineCombination k p) w =
      s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty := rfl

