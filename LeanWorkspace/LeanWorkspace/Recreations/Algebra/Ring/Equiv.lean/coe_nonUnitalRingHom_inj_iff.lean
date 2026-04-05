import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

theorem coe_nonUnitalRingHom_inj_iff {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f g : R ≃+* S) : f = g ↔ (f : R →ₙ+* S) = g := ⟨fun h => by rw [h], fun h => RingEquiv.ext <| NonUnitalRingHom.ext_iff.mp h⟩

