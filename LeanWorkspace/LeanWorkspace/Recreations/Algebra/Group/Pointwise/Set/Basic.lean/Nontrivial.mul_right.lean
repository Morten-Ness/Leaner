import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [IsRightCancelMul α] {s t : Set α}

theorem Nontrivial.mul_right : s.Nontrivial → t.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, Set.mul_mem_mul ha hc, b * c, Set.mul_mem_mul hb hc, by simpa⟩

