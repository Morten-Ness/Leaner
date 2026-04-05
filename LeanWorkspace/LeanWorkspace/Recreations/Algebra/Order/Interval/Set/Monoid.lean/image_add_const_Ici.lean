import Mathlib

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem image_add_const_Ici : (fun x => x + a) '' Ici b = Ici (b + a) := (Set.Ici_add_bij _ _).image_eq

