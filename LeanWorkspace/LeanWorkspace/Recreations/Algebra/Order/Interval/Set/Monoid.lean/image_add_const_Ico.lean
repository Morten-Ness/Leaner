import Mathlib

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem image_add_const_Ico : (fun x => x + a) '' Ico b c = Ico (b + a) (c + a) := (Set.Ico_add_bij _ _ _).image_eq

