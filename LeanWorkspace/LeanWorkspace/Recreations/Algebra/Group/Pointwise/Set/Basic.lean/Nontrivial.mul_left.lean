import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] {s t : Set α}

theorem Nontrivial.mul_left : t.Nontrivial → s.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, Set.mul_mem_mul hc ha, c * b, Set.mul_mem_mul hc hb, by simpa⟩

