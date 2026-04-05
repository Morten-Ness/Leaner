import Mathlib

variable {k G : Type*}

variable [Mul G]

variable {R : Type*} [Semiring R] [NonAssocSemiring k] [SMul G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R]
    [MulHomClass g_hom G R] (f : k →+* R) (g : g_hom) (a b : SkewMonoidAlgebra k G)
    (h_comm : ∀ {x y}, y ∈ a.support → (f (y • b.coeff x)) * g y = (g y) * (f (b.coeff x))) :
    SkewMonoidAlgebra.liftNC (f : k →+ R) g (a * b) = SkewMonoidAlgebra.liftNC (f : k →+ R) g a * SkewMonoidAlgebra.liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← SkewMonoidAlgebra.sum_single a, ← SkewMonoidAlgebra.sum_single b]
  simp_rw [SkewMonoidAlgebra.mul_def, SkewMonoidAlgebra.map_sum, liftNC_single, SkewMonoidAlgebra.sum_mul, SkewMonoidAlgebra.mul_sum]
  refine SkewMonoidAlgebra.sum_congr fun y hy ↦ SkewMonoidAlgebra.sum_congr fun x _hx ↦ ?_
  simp only [AddMonoidHom.coe_coe, map_mul]
  rw [mul_assoc, ← mul_assoc (f (y • b.coeff x)), h_comm hy, mul_assoc, mul_assoc]

