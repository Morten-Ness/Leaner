import Mathlib

variable {M : Type*}

theorem Irreducible.isUnit_iff_not_associated_of_dvd [Monoid M]
    {x y : M} (hx : Irreducible x) (hy : y ∣ x) : IsUnit y ↔ ¬ Associated x y := ⟨fun hy hxy => hx.1 (Associated.symm hxy.isUnit hy), (hx.dvd_iff.mp hy).resolve_right⟩

