import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ ≠ p₂ := by
  rintro rfl
  simp [collinear_pair] at h

