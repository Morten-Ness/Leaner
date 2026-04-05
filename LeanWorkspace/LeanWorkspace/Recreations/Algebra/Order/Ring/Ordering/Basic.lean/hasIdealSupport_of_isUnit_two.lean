import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport := by
  rw [hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (-x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

