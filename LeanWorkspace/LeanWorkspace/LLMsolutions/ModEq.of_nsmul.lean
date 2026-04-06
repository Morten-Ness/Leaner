FAIL
import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem of_nsmul {n : ℕ} : a ≡ b [PMOD n • p] → a ≡ b [PMOD p] := by
  intro h
  rcases h with ⟨z, hz⟩
  refine ⟨n * z, ?_⟩
  rcases hz with ⟨w, hw⟩
  refine ⟨n * w, ?_⟩
  simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hw
