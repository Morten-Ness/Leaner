import Mathlib

variable {M G α β : Type*}

variable (M) [SMul M α] [IsPretransitive M α]

theorem IsPretransitive.of_orbit {X : Type*} [Group G] [MulAction G X] {x₀ : X}
    (ha : ∀ x, ∃ g : G, g • x₀ = x) :
    IsPretransitive G X := by
  constructor
  intro x y
  rcases ha x with ⟨g, rfl⟩
  rcases ha y with ⟨h, rfl⟩
  exact ⟨h * g⁻¹, by simp [mul_smul]⟩

