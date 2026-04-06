FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_const_vsub_eq_sub_weightedVSubOfPoint (w : ι → k) (p₂ : ι → P) (p₁ b : P) :
    (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = (∑ i ∈ s, w i) • (p₁ -ᵥ b) - s.weightedVSubOfPoint p₂ b w := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [Finset.weightedVSubOfPoint]
  | @insert i s his ih =>
      simp [Finset.weightedVSubOfPoint, his, ih, smul_sub, add_comm, add_left_comm, add_assoc,
        sub_eq_add_neg, add_smul, vsub_eq_sub_vsub_cancel_right]
