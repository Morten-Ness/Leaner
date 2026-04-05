import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_list_prod [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) : l.prod.fst = (l.map TrivSqZeroExt.fst).prod := map_list_prod ({ toFun := TrivSqZeroExt.fst, map_one' := TrivSqZeroExt.fst_one, map_mul' := TrivSqZeroExt.fst_mul } : tsze R M →* R) _

