import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.cancel_left [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHom M N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h => OneHom.ext fun x => hg <| by rw [← OneHom.comp_apply, h, OneHom.comp_apply],
    fun h => h ▸ rfl⟩

