import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable {α α₂ β F : Type*} [Semiring β] [Monoid α] [Monoid α₂] [FunLike F α α₂]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem mapDomain_mul [MulSemiringAction α β] [MulSemiringAction α₂ β]
    [MulHomClass F α α₂] {f : F} (x y : SkewMonoidAlgebra β α)
    (hf : ∀ (a : α) (x : β), a • x = (f a) • x) :
    SkewMonoidAlgebra.mapDomain f (x * y) = SkewMonoidAlgebra.mapDomain f x * SkewMonoidAlgebra.mapDomain f y := by
  rw [SkewMonoidAlgebra.mul_def, SkewMonoidAlgebra.map_sum]
  have : (SkewMonoidAlgebra.sum x fun a b ↦ SkewMonoidAlgebra.sum y fun a₂ b₂ ↦ SkewMonoidAlgebra.mapDomain (↑f) (SkewMonoidAlgebra.single (a * a₂) (b * a • b₂))) =
      SkewMonoidAlgebra.sum (SkewMonoidAlgebra.mapDomain (↑f) x) fun a₁ b₁ ↦
        SkewMonoidAlgebra.sum (SkewMonoidAlgebra.mapDomain (↑f) y) fun a₂ b₂ ↦ SkewMonoidAlgebra.single (a₁ * a₂) (b₁ * a₁ • b₂) := by
    simp_rw [SkewMonoidAlgebra.mapDomain_single, map_mul]
    rw [SkewMonoidAlgebra.sum_mapDomain_index (by simp) (by simp [add_mul, SkewMonoidAlgebra.single_add, SkewMonoidAlgebra.sum_add])]
    congr
    ext a b c
    rw [SkewMonoidAlgebra.sum_mapDomain_index (by simp) (by simp [smul_add, mul_add, SkewMonoidAlgebra.single_add])]
    simp_rw [hf]
  convert this using 4
  rw [SkewMonoidAlgebra.map_sum]

