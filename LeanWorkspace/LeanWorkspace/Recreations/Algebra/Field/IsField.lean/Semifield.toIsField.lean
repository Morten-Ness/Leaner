import Mathlib

theorem Semifield.toIsField (R : Type u) [Semifield R] : IsField R where
  __ := ‹Semifield R›
  mul_inv_cancel {a} ha := ⟨a⁻¹, mul_inv_cancel₀ ha⟩

