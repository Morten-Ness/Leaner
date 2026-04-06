import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).weightedVSub p w = s₂.weightedVSub (p ∘ e) (w ∘ e) := by
  classical
  unfold Finset.weightedVSub
  simp [Finset.sum_map]
