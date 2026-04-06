import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_apply_const (w : ι → k) (p : P) (h : ∑ i ∈ s, w i = 0) :
    s.weightedVSub (fun _ => p) w = 0 := by
  classical
  simp [Finset.weightedVSub, h]
