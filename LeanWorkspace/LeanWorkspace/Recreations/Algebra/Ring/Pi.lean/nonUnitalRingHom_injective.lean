import Mathlib

variable {I : Type u}

variable {f : I → Type v}

variable (i : I)

theorem nonUnitalRingHom_injective {γ : Type w} [Nonempty I]
    [∀ i, NonUnitalNonAssocSemiring (f i)] [NonUnitalNonAssocSemiring γ] (g : ∀ i, γ →ₙ+* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (Pi.nonUnitalRingHom g) := mulHom_injective (fun i => (g i).toMulHom) hg

