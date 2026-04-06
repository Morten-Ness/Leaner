FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 0) (b : P) : s.weightedVSub p w = s.weightedVSubOfPoint p b w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at h
      simp [Finset.weightedVSub, Finset.weightedVSubOfPoint]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert, ha, Finset.weightedVSub_insert, Finset.weightedVSubOfPoint_insert] at h ⊢
      rw [ih (by simpa [h])]
      rw [← smul_vsub_assoc, ← add_vsub_assoc]
      congr
      simpa [h, add_comm, add_left_comm, add_assoc] using h
