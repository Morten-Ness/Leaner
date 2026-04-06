FAIL
import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_left_cancel' (c : G) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] := by
  rintro ⟨m, n, h⟩
  refine ⟨n, m, ?_⟩
  have h' := congrArg (fun x => -c + x + a + b) h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'.symm
