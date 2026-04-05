import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.not_injective {R X : Type*} [AddZeroClass R] {f : R → X} {c : R}
    (hf : Function.Periodic f c) (hc : c ≠ 0) : ¬ Function.Injective f := fun h ↦ hc <| h hf.eq

