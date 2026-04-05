import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_id : WithOne.mapMulHom (MulHom.id α) = MonoidHom.id (WithOne α) := by
  ext x
  induction x <;> rfl

