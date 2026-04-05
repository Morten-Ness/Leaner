import Mathlib

variable {M N P σ : Type*}

variable [Mul M]

theorem AddSubsemigroup.toSubsemigroup'_closure (S : Set (Additive M)) :
    AddSubsemigroup.toSubsemigroup' (AddSubsemigroup.closure S) =
      Subsemigroup.closure (Additive.ofMul ⁻¹' S) := le_antisymm
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <|
      AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := Additive M))

