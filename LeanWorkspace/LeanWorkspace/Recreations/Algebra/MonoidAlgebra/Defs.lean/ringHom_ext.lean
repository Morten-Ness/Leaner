import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [MulOneClass M]

theorem ringHom_ext [Semiring S] {f g : R[M] →+* S}
    (h₁ : ∀ r, f (single 1 r) = g (single 1 r)) (h_of : ∀ m, f (single m 1) = g (single m 1)) :
    f = g := RingHom.coe_addMonoidHom_injective <| addHom_ext fun m r ↦ by
    simpa [← map_mul] using congr($(h₁ r) * $(h_of m))

