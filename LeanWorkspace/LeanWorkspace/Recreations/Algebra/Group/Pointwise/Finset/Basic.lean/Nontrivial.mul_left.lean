import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem Nontrivial.mul_left : t.Nontrivial → s.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, Finset.mul_mem_mul hc ha, c * b, Finset.mul_mem_mul hc hb, by simpa⟩

