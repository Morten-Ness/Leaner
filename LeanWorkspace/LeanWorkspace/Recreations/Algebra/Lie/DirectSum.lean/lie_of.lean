import Mathlib

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

variable (L : ι → Type w)

variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

theorem lie_of [DecidableEq ι] {i j : ι} (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = if hij : i = j then of L i ⁅x, hij.symm.recOn y⁆ else 0 := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp only [DirectSum.lie_of_same L x y, dif_pos]
  · simp only [DirectSum.lie_of_of_ne L hij x y, hij, dite_false]

