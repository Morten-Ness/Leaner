import Mathlib

variable {M N P σ : Type*}

variable {A : Type*} [Add A]

theorem AddSubsemigroup.toSubsemigroup_closure (S : Set A) :
    AddSubsemigroup.toSubsemigroup (AddSubsemigroup.closure S) =
      Subsemigroup.closure (Multiplicative.toAdd ⁻¹' S) := le_antisymm
    (AddSubsemigroup.toSubsemigroup.to_galoisConnection.l_le <|
      AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))

