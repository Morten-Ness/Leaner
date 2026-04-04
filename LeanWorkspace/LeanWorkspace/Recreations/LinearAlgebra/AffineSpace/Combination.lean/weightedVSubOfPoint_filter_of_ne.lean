import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_filter_of_ne (w : ι → k) (p : ι → P) (b : P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    {x ∈ s | pred x}.weightedVSubOfPoint p b w = s.weightedVSubOfPoint p b w := by
  rw [Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply, sum_filter_of_ne]
  intro i hi hne
  refine h i hi ?_
  intro hw
  simp [hw] at hne

