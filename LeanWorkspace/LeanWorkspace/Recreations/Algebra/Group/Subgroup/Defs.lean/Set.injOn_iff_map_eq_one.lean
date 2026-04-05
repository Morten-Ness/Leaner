import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem Set.injOn_iff_map_eq_one {F G H S : Type*} [Group G] [Group H]
    [FunLike F G H] [MonoidHomClass F G H] (f : F)
    [SetLike S G] [OneMemClass S G] [MulMemClass S G] [InvMemClass S G] (s : S) :
    Set.InjOn f s ↔ ∀ a ∈ s, f a = 1 → a = 1 where
  mp h a ha ha' := by
    refine h ha (Subgroup.one_mem s) ?_
    rwa [map_one]
  mpr h x hx y hy hxy := by
    refine mul_inv_eq_one.1 <| h _ (Subgroup.mul_mem ?_ (Subgroup.inv_mem ?_)) ?_ <;> simp_all

