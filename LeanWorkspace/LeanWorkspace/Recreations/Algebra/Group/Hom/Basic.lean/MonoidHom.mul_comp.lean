import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOneClass M] [CommMonoid N]

theorem mul_comp [MulOneClass P] (g₁ g₂ : M →* N) (f : P →* M) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

