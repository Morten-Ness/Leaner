import Mathlib

variable {M N P σ : Type*}

variable {A : Type*} [Add A]

theorem Subsemigroup.toAddSubsemigroup'_closure (S : Set (Multiplicative A)) :
    Subsemigroup.toAddSubsemigroup' (Subsemigroup.closure S) =
      AddSubsemigroup.closure (Multiplicative.ofAdd ⁻¹' S) := le_antisymm
    (Subsemigroup.toAddSubsemigroup'.to_galoisConnection.l_le <|
      Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))
    (AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))

