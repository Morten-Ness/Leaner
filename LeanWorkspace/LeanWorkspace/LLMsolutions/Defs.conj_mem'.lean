FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {H : Subgroup G}

theorem conj_mem' (nH : H.Normal) (n : G) (hn : n ∈ H) (g : G) :
    g⁻¹ * n * g ∈ H := by
  exact nH.conj_mem n hn g
