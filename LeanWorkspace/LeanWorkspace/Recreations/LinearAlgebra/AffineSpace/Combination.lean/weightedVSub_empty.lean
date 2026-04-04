import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_empty (w : ι → k) (p : ι → P) : (∅ : Finset ι).weightedVSub p w = (0 : V) := by
  simp [Finset.weightedVSub_apply]

