import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem restrict_range (f : G →* N) : (f.restrict K).range = K.map f := by
  simp_rw [SetLike.ext_iff, MonoidHom.mem_range, mem_map, restrict_apply, SetLike.exists,
    exists_prop, forall_const]

