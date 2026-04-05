import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.cancel_left [MulOne M] [MulOne N] [MulOne P]
    {g : N →* P} {f₁ f₂ : M →* N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ := ⟨fun h => MonoidHom.ext fun x => hg <| by rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩

