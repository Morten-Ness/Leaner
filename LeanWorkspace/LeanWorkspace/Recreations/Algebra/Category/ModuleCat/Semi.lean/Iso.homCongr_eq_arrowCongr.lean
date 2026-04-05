import Mathlib

variable (R : Type u) [Semiring R]

variable {X₁ X₂ : Type v}

variable {S : Type u} [CommSemiring S]

variable {X Y X' Y' : SemimoduleCat.{v} S}

theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquivₛ j.toLinearEquivₛ f.hom⟩ := rfl

