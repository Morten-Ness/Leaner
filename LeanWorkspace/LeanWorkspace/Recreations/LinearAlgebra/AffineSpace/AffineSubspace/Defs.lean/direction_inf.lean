import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_inf (s₁ s₂ : AffineSubspace k P) :
    (s₁ ⊓ s₂).direction ≤ s₁.direction ⊓ s₂.direction := by
  simp only [AffineSubspace.direction_eq_vectorSpan, vectorSpan_def]
  exact
    le_inf (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_left) hp)
      (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_right) hp)

