FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_const_vsub_eq_neg_weightedVSub (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 0) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = -s.weightedVSub p₂ w := by
  classical
  simpa [Finset.weightedVSub, h, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (s.sum_vsub_eq_sub_sum p₁ fun i => w i • p₂ i)
