import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

set_option backward.isDefEq.respectTransparency false in
theorem hasTrivialRadical_iff_no_abelian_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsLieAbelian I → I = ⊥ := by
  rw [LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals]
  constructor <;> intro h₁ I h₂
  · exact h₁ _ <| LieAlgebra.ofAbelianIsSolvable I
  · rw [← abelian_of_solvable_ideal_eq_bot_iff]
    exact h₁ _ <| abelian_derivedAbelianOfIdeal I

