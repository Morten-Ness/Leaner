import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq : Subgroup.closure (K : Set G) = K := (Subgroup.gi G).l_u_eq K

