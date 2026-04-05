import Mathlib

variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)

theorem IsOrderedMonoid.mkOfCone [GroupConeClass S G] :
    let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
    IsOrderedMonoid G :=
  let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }

