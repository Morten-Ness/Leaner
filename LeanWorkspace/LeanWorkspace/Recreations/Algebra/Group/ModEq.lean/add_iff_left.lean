import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_iff_left (h : a ≡ b [PMOD p]) :
    a + c ≡ b + d [PMOD p] ↔ c ≡ d [PMOD p] := by
  refine ⟨fun hadd ↦ ?_, AddCommGroup.ModEq.add h⟩
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  rcases hadd with ⟨m, n, hadd⟩
  use m + l, n + k
  apply add_right_cancel (b := a)
  rw [add_assoc, add_comm c, AddCommGroup.ModEq.add_nsmul, add_right_comm, hadd, ← add_assoc, add_right_comm _ b,
    add_right_comm _ b, add_assoc, ← h, add_add_add_comm, AddCommGroup.ModEq.add_nsmul, ← add_assoc]

