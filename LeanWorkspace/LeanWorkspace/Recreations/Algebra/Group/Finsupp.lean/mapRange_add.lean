import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem mapRange_add {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : ι →₀ M) :
    mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ := ext fun _ => by simp only [hf', Finsupp.add_apply, mapRange_apply]

