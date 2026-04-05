import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem map_equiv_normalizer_eq (H : Subgroup G) (f : G ≃* N) :
    (normalizer H).map f.toMonoidHom = normalizer (H.map f.toMonoidHom) := by
  ext x
  simp only [mem_normalizer_iff, mem_map_equiv]
  rw [f.toEquiv.forall_congr]
  intro
  simp

