import Mathlib

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem image_add_const_Ioi : (fun x => x + a) '' Ioi b = Ioi (b + a) := (Set.Ioi_add_bij _ _).image_eq

