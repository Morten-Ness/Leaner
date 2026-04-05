import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [Semiring R]

variable [AddMonoid A] [AddMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

theorem le_inf_support_list_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (l : List R[A]) :
    (l.map fun f : R[A] => f.support.inf degt).sum ≤ l.prod.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr ?_
  refine AddMonoidAlgebra.sup_support_list_prod_le ?_ ?_ l
  · refine (OrderDual.ofDual_le_ofDual.mp ?_)
    exact degt0
  · refine (fun a b => OrderDual.ofDual_le_ofDual.mp ?_)
    exact degtm a b

