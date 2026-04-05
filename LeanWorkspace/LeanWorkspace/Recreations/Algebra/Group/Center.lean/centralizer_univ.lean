import Mathlib

variable {M : Type*} {S T : Set M}

variable [Semigroup M] {a b : M}

theorem centralizer_univ : Set.centralizer univ = Set.center M := Subset.antisymm (fun _ ha ↦ Semigroup.mem_center_iff.mpr fun b ↦ ha b (Set.mem_univ b))
  fun _ ha b _ ↦ (ha.comm b).symm

-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`

