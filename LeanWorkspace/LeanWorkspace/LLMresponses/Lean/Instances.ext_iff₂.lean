import Mathlib

universe uM uN uP uQ

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem ext_iff₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} {f g : M →* N →* P} :
    f = g ↔ ∀ x : M, ∀ y : N, f x y = g x y := by
  constructor
  · intro h x y
    rw [h]
  · intro h
    ext x y
    exact h x y
