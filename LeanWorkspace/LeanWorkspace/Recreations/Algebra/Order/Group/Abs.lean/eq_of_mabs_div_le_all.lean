import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem eq_of_mabs_div_le_all [DenselyOrdered G] {x y : G} (h : ∀ ε > 1, |x / y|ₘ ≤ ε) : x = y := eq_of_mabs_div_le_one <| forall_gt_imp_ge_iff_le_of_dense.mp h

