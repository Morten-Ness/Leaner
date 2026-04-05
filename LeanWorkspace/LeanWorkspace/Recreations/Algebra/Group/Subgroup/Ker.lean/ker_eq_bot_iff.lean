import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_eq_bot_iff (f : G →* M) : f.ker = ⊥ ↔ Function.Injective f := ⟨fun h x y hxy => by rwa [MonoidHom.eq_iff, h, mem_bot, inv_mul_eq_one, eq_comm] at hxy, fun h =>
    bot_unique fun _ hx => h (hx.trans f.map_one.symm)⟩

