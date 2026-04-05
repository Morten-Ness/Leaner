import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem copy_eq (K : Subgroup G) (s : Set G) (hs : s = ↑K) : K.copy s hs = K := SetLike.coe_injective hs

