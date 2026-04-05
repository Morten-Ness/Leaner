import Mathlib

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

variable (L : ι → Type w)

variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

theorem lie_of_same [DecidableEq ι] {i : ι} (x y : L i) :
    ⁅of L i x, of L i y⁆ = of L i ⁅x, y⁆ := DFinsupp.zipWith_single_single _ _ _ _

