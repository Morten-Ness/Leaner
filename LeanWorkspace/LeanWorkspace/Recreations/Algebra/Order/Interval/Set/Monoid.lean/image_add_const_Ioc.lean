import Mathlib

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem image_add_const_Ioc : (fun x => x + a) '' Ioc b c = Ioc (b + a) (c + a) := (Set.Ioc_add_bij _ _ _).image_eq

