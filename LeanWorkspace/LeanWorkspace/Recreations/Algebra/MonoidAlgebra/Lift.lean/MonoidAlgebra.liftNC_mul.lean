import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

variable [Semiring k] [Mul G] [Semiring R]

theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R] [MulHomClass g_hom G R]
    (f : k →+* R) (g : g_hom) (a b : k[G])
    (h_comm : ∀ {x y}, y ∈ a.support → Commute (f (b x)) (g y)) :
    MonoidAlgebra.liftNC (f : k →+ R) g (a * b) = MonoidAlgebra.liftNC (f : k →+ R) g a * MonoidAlgebra.liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← sum_single a, ← sum_single b]
  simp_rw [mul_def, map_finsuppSum, MonoidAlgebra.liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

