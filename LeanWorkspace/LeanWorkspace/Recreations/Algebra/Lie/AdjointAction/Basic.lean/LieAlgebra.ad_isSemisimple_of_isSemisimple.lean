import Mathlib

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

theorem LieAlgebra.ad_isSemisimple_of_isSemisimple {a : Module.End K V} (ha : a.IsSemisimple) :
    (LieAlgebra.ad K (Module.End K V) a).IsSemisimple := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : Module.End.IsSemisimple (LinearMap.mulLeft K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have : Polynomial.aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    simpa using this
  have hr : Module.End.IsSemisimple (LinearMap.mulRight K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have hrw : LinearMap.mulRight K a =
        (Algebra.lsmul (A := (Module.End K V)ᵐᵒᵖ) K K (Module.End K V)) (.op a) := by
      ext; simp [Algebra.lsmul]
    rw [hrw, Polynomial.aeval_algHom_apply, Polynomial.aeval_op_apply, minpoly.aeval,
      MulOpposite.op_zero, map_zero]
  exact hl.sub_of_commute (LinearMap.commute_mulLeft_right a a) hr

