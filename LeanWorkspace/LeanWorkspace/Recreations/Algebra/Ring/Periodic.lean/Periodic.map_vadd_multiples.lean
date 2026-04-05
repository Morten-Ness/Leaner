import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.map_vadd_multiples [AddCommMonoid α] (hf : Function.Periodic f c)
    (a : AddSubmonoid.multiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubmonoid.vadd_def, add_comm _ x, hf.nsmul m x]

