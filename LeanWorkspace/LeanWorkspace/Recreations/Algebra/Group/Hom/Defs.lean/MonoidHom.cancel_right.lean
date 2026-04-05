import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.cancel_right [MulOne M] [MulOne N] [MulOne P]
    {g₁ g₂ : N →* P} {f : M →* N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := ⟨fun h => MonoidHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

