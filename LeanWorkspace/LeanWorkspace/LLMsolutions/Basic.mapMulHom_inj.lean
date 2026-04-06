import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_inj {f g : α →ₙ* β} : WithOne.mapMulHom f = WithOne.mapMulHom g ↔ f = g := by
  constructor
  · intro h
    ext a
    have h' := congrArg (fun k => k (some a)) h
    change some (f a) = some (g a) at h'
    exact Option.some.inj h'
  · intro h
    cases h
    rfl
