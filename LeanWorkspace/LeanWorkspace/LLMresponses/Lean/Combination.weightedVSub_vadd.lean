import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_vadd {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → P) (v : V) :
    s.weightedVSub (v +ᵥ p) w = s.weightedVSub p w := by
  classical
  simpa [Finset.weightedVSub_vadd, h] using s.weightedVSub_vadd p w v
