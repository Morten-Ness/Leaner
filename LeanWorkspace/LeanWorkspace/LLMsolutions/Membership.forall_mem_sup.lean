import Mathlib

variable {M A B : Type*}

variable {N : Type*} [CommMonoid N]

variable {P : N → Prop}

theorem forall_mem_sup {s t : Submonoid N} :
    (∀ x ∈ s ⊔ t, P x) ↔ (∀ x₁ ∈ s, ∀ x₂ ∈ t, P (x₁ * x₂)) := by
  constructor
  · intro h x₁ hx₁ x₂ hx₂
    apply h (x₁ * x₂)
    exact Submonoid.mul_mem_sup hx₁ hx₂
  · intro h x hx
    rcases Submonoid.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    exact h y hy z hz
