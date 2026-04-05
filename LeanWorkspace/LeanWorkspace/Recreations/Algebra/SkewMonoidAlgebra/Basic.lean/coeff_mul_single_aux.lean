import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Mul G] [SMulZeroClass G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_mul_single_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
    (H : ∀ a, a * x = z ↔ a = y) : (f * SkewMonoidAlgebra.single x r).coeff z = f.coeff y * y • r := by
  classical
  have A : ∀ a₁ b₁, ((SkewMonoidAlgebra.single x r).sum fun a₂ b₂ ↦ ite (a₁ * a₂ = z) (b₁ * a₁ • b₂) 0) =
      ite (a₁ * x = z) (b₁ * a₁ • r) 0 :=
    fun a₁ b₁ ↦ SkewMonoidAlgebra.sum_single_index <| by simp
  calc
    (f * (SkewMonoidAlgebra.single x r)).coeff z =
        SkewMonoidAlgebra.sum f fun a b ↦ if a = y then b * y • r else 0 := by simp [SkewMonoidAlgebra.coeff_mul, A, H, SkewMonoidAlgebra.sum_ite_eq']
    _ = if y ∈ f.support then f.coeff y * y • r else 0 := (SkewMonoidAlgebra.sum_ite_eq' f.support _ _)
    _ = f.coeff y * y • r := by
      split_ifs with h <;> simp [SkewMonoidAlgebra.support] at h <;> simp [h]

