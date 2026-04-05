import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem closure_preimage_le (f : G →* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f := (closure_le _).2 fun x hx => by rw [SetLike.mem_coe, Subgroup.mem_comap]; exact subset_closure hx

