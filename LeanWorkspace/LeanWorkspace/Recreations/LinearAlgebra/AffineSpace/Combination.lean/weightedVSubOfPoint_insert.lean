import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_insert [DecidableEq ι] (w : ι → k) (p : ι → P) (i : ι) :
    (insert i s).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply]
  apply sum_insert_zero
  rw [vsub_self, smul_zero]

