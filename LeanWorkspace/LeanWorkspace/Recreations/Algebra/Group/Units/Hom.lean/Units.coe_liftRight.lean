import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem coe_liftRight {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    (Units.liftRight f g h x : N) = f x := h x

