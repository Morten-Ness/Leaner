import Mathlib

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

variable (L : ι → Type w)

variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

theorem lieAlgebra_ext {x y : ⨁ i, L i}
    (h : ∀ i, DirectSum.lieAlgebraComponent R ι L i x = DirectSum.lieAlgebraComponent R ι L i y) : x = y := DFinsupp.ext h

