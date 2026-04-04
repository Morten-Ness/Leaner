import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_vadd {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → P) (v : V) :
    s.weightedVSub (v +ᵥ p) w = s.weightedVSub p w := by
  rw [Finset.weightedVSub, Finset.weightedVSubOfPoint_vadd,
    Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

