import Mathlib

section

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [MulOneClass β]

variable (f : α →ₙ* β)

theorem lift_unique (f : WithOne α →* β) : f = WithOne.lift (f.toMulHom.comp WithOne.coeMulHom) := (WithOne.lift.apply_symm_apply f).symm

end

section

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_comp (f : α →ₙ* β) (g : β →ₙ* γ) :
    WithOne.mapMulHom (g.comp f) = (WithOne.mapMulHom g).comp (WithOne.mapMulHom f) := MonoidHom.ext fun x => (WithOne.mapMulHom_mapMulHom f g x).symm

end

section

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem mapMulHom_inj {f g : α →ₙ* β} : WithOne.mapMulHom f = WithOne.mapMulHom g ↔ f = g := WithOne.mapMulHom_injective'.eq_iff

end
