FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop} [DecidablePred pred]
    (h : ∀ i ∈ s, w i ≠ 0 → pred i) : {x ∈ s | pred x}.weightedVSub p w = s.weightedVSub p w := by
  classical
  by_cases hs : s.Nonempty
  · rcases hs with ⟨i, hi⟩
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_vadd_of_sum_eq_zero _ _ _ i hi,
      Finset.weightedVSub_eq_weightedVSubOfPoint_vadd_of_sum_eq_zero _ _ _ i
        (by simp [hi, h i hi])]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
