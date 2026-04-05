import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Group G] [MulSemiringAction G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_mul_left (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = f.sum fun a b ↦ b * a • g.coeff (a⁻¹ * x) := calc
    (f * g).coeff x = SkewMonoidAlgebra.sum f fun a b ↦ (SkewMonoidAlgebra.single a b * g).coeff x := by
      rw [← SkewMonoidAlgebra.coeff_sum, ← SkewMonoidAlgebra.sum_mul g f, SkewMonoidAlgebra.sum_single f]
    _ = _ := by simp

