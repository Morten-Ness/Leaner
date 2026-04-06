import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_compl : a • sᶜ = (a • s)ᶜ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ hx
    apply hy
    rcases hx with ⟨z, hz, hz_eq⟩
    have : z = y := by
      apply smul_left_cancel a
      simpa [hz_eq]
    simpa [this] using hz
  · intro hx
    refine ⟨a⁻¹ • x, ?_, by simp [smul_smul]⟩
    intro hs
    apply hx
    refine ⟨a⁻¹ • x, hs, by simp [smul_smul]⟩
