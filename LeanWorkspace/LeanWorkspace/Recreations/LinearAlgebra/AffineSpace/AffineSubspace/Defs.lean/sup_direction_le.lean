import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem sup_direction_le (s₁ s₂ : AffineSubspace k P) :
    s₁.direction ⊔ s₂.direction ≤ (s₁ ⊔ s₂).direction := by
  simp only [AffineSubspace.direction_eq_vectorSpan, vectorSpan_def]
  exact
    sup_le
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_left : s₁ ≤ s₁ ⊔ s₂)) hp)
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_right : s₂ ≤ s₁ ⊔ s₂)) hp)

