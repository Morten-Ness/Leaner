import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_indicator_subset (w : ι → k) (p : ι → P) (b : P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint p b (Set.indicator (↑s₁) w) := by
  rw [Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply]
  exact Eq.symm <|
    sum_indicator_subset_of_eq_zero w (fun i wi => wi • (p i -ᵥ b : V)) h fun i => zero_smul k _

