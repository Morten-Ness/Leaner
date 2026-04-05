import Mathlib

variable (R : Type u) [Ring R]

variable {X₁ X₂ : Type v}

variable {S : Type u} [CommRing S]

variable {X Y X' Y' : ModuleCat.{v} S}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquiv f.hom⟩ := rfl

