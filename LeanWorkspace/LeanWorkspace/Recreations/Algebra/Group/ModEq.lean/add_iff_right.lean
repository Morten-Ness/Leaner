import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_iff_right (h : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] ↔ a ≡ b [PMOD p] := by
  simpa only [add_comm c, add_comm d] using AddCommGroup.ModEq.add_iff_left h

protected alias ⟨add_left_cancel, _⟩ := AddCommGroup.ModEq.add_iff_left

protected alias ⟨add_right_cancel, _⟩ := AddCommGroup.ModEq.add_iff_right

