import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_apply_const (w : ι → k) (p : P) (b : P) :
    s.weightedVSubOfPoint (fun _ => p) b w = (∑ i ∈ s, w i) • (p -ᵥ b) := by
  rw [Finset.weightedVSubOfPoint_apply, sum_smul]

