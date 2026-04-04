import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_sInf (t : Set (AffineSubspace k P)) :
    AffineSubspace.direction (sInf t) ≤ ⨅ s ∈ t, s.direction := by
  simp only [AffineSubspace.direction_eq_vectorSpan, vectorSpan_def]
  exact le_iInf₂ fun s hs => Submodule.span_mono <| vsub_self_mono <| biInter_subset_of_mem hs

