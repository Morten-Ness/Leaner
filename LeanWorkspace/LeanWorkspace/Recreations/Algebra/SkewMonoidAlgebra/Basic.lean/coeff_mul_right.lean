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

theorem coeff_mul_right (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = g.sum fun a b ↦ f.coeff (x * a⁻¹) * (x * a⁻¹) • b := calc
    (f * g).coeff x = SkewMonoidAlgebra.sum g fun a b ↦ (f * SkewMonoidAlgebra.single a b).coeff x := by
      rw [← SkewMonoidAlgebra.coeff_sum, ← SkewMonoidAlgebra.mul_sum f g, SkewMonoidAlgebra.sum_single g]
    _ = _ := by simp

