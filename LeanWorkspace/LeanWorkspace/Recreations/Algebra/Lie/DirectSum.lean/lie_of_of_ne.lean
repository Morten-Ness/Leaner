import Mathlib

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

variable (L : ι → Type w)

variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

theorem lie_of_of_ne [DecidableEq ι] {i j : ι} (hij : i ≠ j) (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = 0 := by
  ext k
  rw [DirectSum.bracket_apply]
  obtain rfl | hik := Decidable.eq_or_ne k i
  · rw [of_eq_of_ne _ _ _ hij, lie_zero, zero_apply]
  · rw [of_eq_of_ne _ _ _ hik, zero_lie, zero_apply]

