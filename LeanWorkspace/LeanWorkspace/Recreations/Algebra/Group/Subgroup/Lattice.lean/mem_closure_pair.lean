import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mem_closure_pair {x y z : C} :
    z ∈ Subgroup.closure ({x, y} : Set C) ↔ ∃ m n : ℤ, x ^ m * y ^ n = z := by
  rw [← Set.singleton_union, Subgroup.closure_union, Subgroup.mem_sup]
  simp_rw [Subgroup.mem_closure_singleton, exists_exists_eq_and]

