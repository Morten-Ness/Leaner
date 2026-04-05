import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_injective' :
    Function.Injective (WithOne.mapMulHom (α := α) (β := β)) :=
  fun f g h ↦ MulHom.ext fun x ↦ coe_injective <| by simp only [← WithOne.mapMulHom_coe, h]

