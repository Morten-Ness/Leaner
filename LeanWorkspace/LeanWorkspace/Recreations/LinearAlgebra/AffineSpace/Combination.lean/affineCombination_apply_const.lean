import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_apply_const (w : ι → k) (p : P) (h : ∑ i ∈ s, w i = 1) :
    s.affineCombination k (fun _ => p) w = p := by
  rw [Finset.affineCombination_apply, s.weightedVSubOfPoint_apply_const, h, one_smul, vsub_vadd]

