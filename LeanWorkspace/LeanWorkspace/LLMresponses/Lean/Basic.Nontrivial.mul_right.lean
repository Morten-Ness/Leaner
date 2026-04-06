import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem Nontrivial.mul_right : s.Nontrivial → t.Nonempty → (s * t).Nontrivial := by
  intro hs ht
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  rcases ht with ⟨z, hz⟩
  refine ⟨x * z, ?_, y * z, ?_, ?_⟩
  · exact Finset.mem_mul.mpr ⟨x, hx, z, hz, rfl⟩
  · exact Finset.mem_mul.mpr ⟨y, hy, z, hz, rfl⟩
  · intro h
    apply hxy
    exact mul_right_cancel h
