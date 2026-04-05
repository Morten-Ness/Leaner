import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem div_mem_ker_iff (f : G →* M) {x y : G} : x / y ∈ MonoidHom.ker f ↔ f x = f y := by
  constructor <;> intro h
  · rw [← div_mul_cancel x y, map_mul, MonoidHom.mem_ker.mp h, one_mul]
  · rw [MonoidHom.mem_ker, div_eq_mul_inv, map_mul, h, ← map_mul, mul_inv_cancel, map_one]

