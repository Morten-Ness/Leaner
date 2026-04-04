import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem mem_sInf_iff (p : P) (t : Set (AffineSubspace k P)) : p ∈ sInf t ↔ ∀ s ∈ t, p ∈ s := Set.mem_iInter₂

