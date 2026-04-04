import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem affineCombination_apply_eq_lineMap_sum [DecidableEq ι] (w : ι → k) (p : ι → P)
    (p₁ p₂ : P) (s' : Finset ι) (h : ∑ i ∈ s, w i = 1) (hp₂ : ∀ i ∈ s ∩ s', p i = p₂)
    (hp₁ : ∀ i ∈ s \ s', p i = p₁) :
    s.affineCombination k p w = AffineMap.lineMap p₁ p₂ (∑ i ∈ s ∩ s', w i) := by
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h p₁,
    Finset.weightedVSubOfPoint_apply, ← s.sum_inter_add_sum_diff s', AffineMap.lineMap_apply,
    vadd_right_cancel_iff, sum_smul]
  convert add_zero _ with i hi
  · convert Finset.sum_const_zero with i hi
    simp [hp₁ i hi]
  · exact (hp₂ i hi).symm

