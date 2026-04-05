import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_list_prod [Monoid R] [AddCommMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) :
    l.prod.snd =
      (l.zipIdx.map fun x : tsze R M × ℕ =>
          ((l.map TrivSqZeroExt.fst).take x.2).prod •> x.fst.snd <• ((l.map TrivSqZeroExt.fst).drop x.2.succ).prod).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons']
    simp_rw [List.map_cons, List.map_map, Function.comp_def, Prod.map_snd, Prod.map_fst, id,
      List.take_zero, List.take_succ_cons, List.prod_nil, List.prod_cons, TrivSqZeroExt.snd_mul, one_smul,
      List.drop, mul_smul, List.sum_cons, TrivSqZeroExt.fst_list_prod, ih, List.smul_sum, List.map_map,
      ← smul_comm (_ : R) (_ : Rᵐᵒᵖ)]
    exact add_comm _ _

