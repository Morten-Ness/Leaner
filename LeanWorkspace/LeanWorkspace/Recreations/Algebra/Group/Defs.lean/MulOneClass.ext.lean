import Mathlib

variable {G : Type*}

theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro @⟨@⟨⟨one₁⟩, ⟨mul₁⟩⟩, one_mul₁, mul_one₁⟩ @⟨@⟨⟨one₂⟩, ⟨mul₂⟩⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME (See https://github.com/leanprover/lean4/issues/1711)
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

