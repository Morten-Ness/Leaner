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

theorem coeff_single_mul_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
    (H : ∀ a, x * a = y ↔ a = z) : (SkewMonoidAlgebra.single x r * f).coeff y = r * x • f.coeff z := by
  classical
  have : (f.sum fun a b ↦ ite (x * a = y) (0 * x • b) 0) = 0 := by simp
  calc
    (SkewMonoidAlgebra.single x r * f).coeff y =
        SkewMonoidAlgebra.sum f fun a b ↦ ite (x * a = y) (r * x • b) 0 :=
      (SkewMonoidAlgebra.coeff_mul _ _ _).trans <| SkewMonoidAlgebra.sum_single_index this
    _ = f.sum fun a b ↦ ite (a = z) (r * x • b) 0 := by simp [H]
    _ = if z ∈ f.support then r * x • f.coeff z else 0 := (SkewMonoidAlgebra.sum_ite_eq' f.support _ _)
    _ = _ := by split_ifs with h <;> simp [SkewMonoidAlgebra.support] at h <;> simp [h]

