import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable {G : Type*} [Group G]

theorem isSMulRegular_of_group [MulAction G R] (g : G) : IsSMulRegular R g := by
  intro x y h
  convert congr_arg (g⁻¹ • ·) h using 1 <;> simp [← smul_assoc]

