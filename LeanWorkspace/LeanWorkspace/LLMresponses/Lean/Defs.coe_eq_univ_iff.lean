import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem coe_eq_univ_iff (Q : AffineSubspace k P) : (Q : Set P) = Set.univ ↔ Q = ⊤ := by
  constructor
  · intro h
    ext p
    change p ∈ (Q : Set P) ↔ p ∈ (⊤ : AffineSubspace k P)
    rw [h]
    simp
  · intro h
    rw [h]
    rfl
