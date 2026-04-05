import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem mul_comm_of_mem_isMulCommutative [IsMulCommutative H] {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    a * b = b * a := setLike_mul_comm ha hb

