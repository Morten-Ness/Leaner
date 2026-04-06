import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w - s₂.weightedVSubOfPoint p b (-w) =
      s.weightedVSubOfPoint p b w := by
  classical
  simp [Finset.weightedVSubOfPoint, h, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    smul_add, add_smul, neg_smul, Finset.sum_sdiff]
