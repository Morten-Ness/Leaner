import Mathlib

variable {M N P σ : Type*}

variable [Mul M]

theorem Subsemigroup.toAddSubsemigroup_closure (S : Set M) :
    Subsemigroup.toAddSubsemigroup (Subsemigroup.closure S) =
    AddSubsemigroup.closure (Additive.toMul ⁻¹' S) := le_antisymm
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <|
      Subsemigroup.closure_le.2 (AddSubsemigroup.subset_closure (M := Additive M)))
    (AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))

