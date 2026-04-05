import Mathlib

variable {M : Type*} {S T : Set M}

variable [CommSemigroup M]

theorem center_eq_univ : Set.center M = univ := (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)

