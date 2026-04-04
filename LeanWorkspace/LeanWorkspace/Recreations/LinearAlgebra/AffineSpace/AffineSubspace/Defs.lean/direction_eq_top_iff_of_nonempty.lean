import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    s.direction = ⊤ ↔ s = ⊤ := by
  constructor
  · intro hd
    rw [← AffineSubspace.direction_top k V P] at hd
    refine AffineSubspace.ext_of_direction_eq hd ?_
    simp [h]
  · rintro rfl
    simp

