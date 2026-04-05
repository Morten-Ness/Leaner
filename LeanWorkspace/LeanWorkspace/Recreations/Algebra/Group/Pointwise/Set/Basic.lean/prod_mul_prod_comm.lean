import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem prod_mul_prod_comm [Mul β] (s₁ s₂ : Set α) (t₁ t₂ : Set β) :
    (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) := by ext; simp [Set.mem_mul]; aesop

