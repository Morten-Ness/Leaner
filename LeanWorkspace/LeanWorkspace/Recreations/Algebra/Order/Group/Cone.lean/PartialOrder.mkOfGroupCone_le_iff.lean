import Mathlib

variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)

theorem PartialOrder.mkOfGroupCone_le_iff {S G : Type*} [CommGroup G] [SetLike S G]
    [GroupConeClass S G] {C : S} {a b : G} :
    (mkOfGroupCone C).le a b ↔ b / a ∈ C := Iff.rfl

