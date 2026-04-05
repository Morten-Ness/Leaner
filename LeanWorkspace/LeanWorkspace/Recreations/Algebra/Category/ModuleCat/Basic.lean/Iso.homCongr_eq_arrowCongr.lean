import Mathlib

variable (R : Type u) [Ring R]

variable {X₁ X₂ : Type v}

variable {S : Type u} [CommRing S]

variable {X Y X' Y' : ModuleCat.{v} S}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquiv j.toLinearEquiv f.hom⟩ := rfl

