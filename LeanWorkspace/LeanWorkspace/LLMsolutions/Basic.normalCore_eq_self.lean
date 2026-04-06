FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_eq_self (H : Subgroup G) [H.Normal] : H.normalCore = H := by
  ext g
  constructor
  · intro hg
    simpa using hg 1
  · intro hg
    intro a
    simpa [mul_assoc] using H.normal_conj_mem hg a
