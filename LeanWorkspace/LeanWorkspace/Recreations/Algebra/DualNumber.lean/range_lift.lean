import Mathlib

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem range_lift
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (DualNumber.lift fe).range = fe.1.1.range ⊔ R[fe.1.2] := by
  simp_rw [← Algebra.map_top, ← DualNumber.range_inlAlgHom_sup_adjoin_eps, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, Set.image_singleton, lift_apply_eps, lift_comp_inlHom,
    Algebra.map_top]

