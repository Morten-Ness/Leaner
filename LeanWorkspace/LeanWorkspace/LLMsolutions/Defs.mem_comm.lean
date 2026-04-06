FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {H : Subgroup G}

theorem mem_comm (nH : H.Normal) {a b : G} (h : a * b ∈ H) : b * a ∈ H := by
  rw [Subgroup.normal_iff] at nH
  exact nH a (a * b) h
