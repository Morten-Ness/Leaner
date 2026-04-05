FAIL
import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem Nontrivial.mul_left : t.Nontrivial → s.Nonempty → (s * t).Nontrivial := by
  intro ht hs
  rcases hs with ⟨a, ha⟩
  rcases ht with ⟨b, hb, c, hc, hbc⟩
  refine ⟨a * b, ?_, a * c, ?_, ?_⟩
  · exact Finset.mem_mul.mpr ⟨a, ha, b, hb, rfl⟩
  · exact Finset.mem_mul.mpr ⟨a, ha, c, hc, rfl⟩
  · intro h
    apply hbc
    exact IsLeftCancelMul.left_cancel h
