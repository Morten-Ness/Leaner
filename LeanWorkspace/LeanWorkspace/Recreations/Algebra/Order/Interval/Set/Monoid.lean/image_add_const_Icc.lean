import Mathlib

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem image_add_const_Icc : (fun x => x + a) '' Icc b c = Icc (b + a) (c + a) := (Set.Icc_add_bij _ _ _).image_eq

