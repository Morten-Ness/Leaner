import Mathlib

variable {ι α β : Type*}

variable [CommGroup α] [Preorder α] [IsOrderedMonoid α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem Monovary.div_left (h₁ : Monovary f₁ g) (h₂ : Antivary f₂ g) : Monovary (f₁ / f₂) g := fun _i _j hij ↦ div_le_div'' (h₁ hij) (h₂ hij)

