import Mathlib

variable (R : Type u) [Semiring R]

variable {X₁ X₂ : Type v}

variable {S : Type u} [CommSemiring S]

variable {X Y X' Y' : SemimoduleCat.{v} S}

theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquivₛ f.hom⟩ := rfl

