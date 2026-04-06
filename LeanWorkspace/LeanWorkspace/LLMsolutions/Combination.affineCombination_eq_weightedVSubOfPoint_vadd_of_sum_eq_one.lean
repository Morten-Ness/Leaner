import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 1) (b : P) :
    s.affineCombination k p w = s.weightedVSubOfPoint p b w +ᵥ b := by
  simpa [Finset.weightedVSubOfPoint, h] using
    (Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      (s := s) (k := k) (w := w) (p := p) h b)
