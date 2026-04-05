import Mathlib

variable {M : Type*}

theorem Associated.of_mul_left [CommMonoidWithZero M] [IsCancelMulZero M] {a b c d : M}
    (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c) (ha : a ≠ 0) : b ~ᵤ d := let ⟨u, hu⟩ := h
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u * (v : Mˣ),
    mul_left_cancel₀ ha
      (by
        rw [← hv, mul_assoc c (v : M) d, mul_left_comm c, ← hu]
        simp [Associated.symm hv, mul_comm, mul_left_comm])⟩

