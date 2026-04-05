import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_const_smul (w : ι → k) (p : ι → P) (c : k) :
    s.weightedVSub p (c • w) = c • s.weightedVSub p w := Finset.weightedVSubOfPoint_const_smul s _ _ _ _

instance : AddTorsor (ι → k) (ι → k) := Pi.instAddTorsor

