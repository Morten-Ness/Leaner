import Mathlib

variable {ι F M N O G H : Type*}

theorem mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x - y) = f x - f y) (v₁ v₂ : ι →₀ G) :
    mapRange f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂ := ext fun _ => by simp only [hf', Finsupp.sub_apply, mapRange_apply]

