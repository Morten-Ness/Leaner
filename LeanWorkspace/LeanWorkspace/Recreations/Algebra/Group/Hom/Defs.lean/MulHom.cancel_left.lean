import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : N →ₙ* P} {f₁ f₂ : M →ₙ* N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h => MulHom.ext fun x => hg <| by rw [← MulHom.comp_apply, h, MulHom.comp_apply],
    fun h => h ▸ rfl⟩

