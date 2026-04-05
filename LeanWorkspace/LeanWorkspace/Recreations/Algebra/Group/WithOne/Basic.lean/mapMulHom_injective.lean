import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_injective {f : α →ₙ* β} (hf : Function.Injective f) :
    Function.Injective (WithOne.mapMulHom f)
  | none, none, _ => rfl
  | (a₁ : α), (a₂ : α), H => by simpa [hf.eq_iff] using H
