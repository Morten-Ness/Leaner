FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) : (s \ s₂).weightedVSub p w - s₂.weightedVSub p (-w) = s.weightedVSub p w := by
  classical
  let p₀ : P := p (Classical.choice <| Finset.nonempty_of_ne_empty <| by
    intro hs
    simpa [hs] using h)
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero p₀]
  · rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero p₀]
    · rw [Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply,
        Finset.weightedVSubOfPoint_apply, sub_eq_add_neg, Finset.sum_sdiff h]
      simp
    · simp
  · simp
