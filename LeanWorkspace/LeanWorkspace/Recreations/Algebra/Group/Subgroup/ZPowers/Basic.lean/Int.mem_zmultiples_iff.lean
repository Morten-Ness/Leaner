import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Int.mem_zmultiples_iff {a b : ℤ} : b ∈ AddSubgroup.zmultiples a ↔ a ∣ b := exists_congr fun k => by rw [mul_comm, eq_comm, ← smul_eq_mul]

