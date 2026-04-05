import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem toAddSubgroup'_closure {A : Type*} [AddGroup A] (S : Set (Multiplicative A)) :
    (Subgroup.closure S).toAddSubgroup' = AddSubgroup.closure (Multiplicative.ofAdd ⁻¹' S) := le_antisymm (toAddSubgroup'.to_galoisConnection.l_le <|
      (Subgroup.closure_le _).mpr <| AddSubgroup.subset_closure (G := A))
    ((AddSubgroup.closure_le _).mpr <| Subgroup.subset_closure (G := Multiplicative A))

