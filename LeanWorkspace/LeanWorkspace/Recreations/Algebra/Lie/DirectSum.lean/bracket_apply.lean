import Mathlib

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

variable (L : ι → Type w)

variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

theorem bracket_apply (x y : ⨁ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ := zipWith_apply _ _ x y i

