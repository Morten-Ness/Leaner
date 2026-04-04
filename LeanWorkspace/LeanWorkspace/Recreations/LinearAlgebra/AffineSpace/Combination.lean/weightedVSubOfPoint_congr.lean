import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) (b : P) :
    s.weightedVSubOfPoint p₁ b w₁ = s.weightedVSubOfPoint p₂ b w₂ := by
  simp_rw [Finset.weightedVSubOfPoint_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [hw i hi, hp i hi]

