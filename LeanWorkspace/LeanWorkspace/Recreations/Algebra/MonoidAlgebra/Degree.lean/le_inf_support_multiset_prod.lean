import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddCommMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

theorem le_inf_support_multiset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (m : Multiset R[A]) :
    (m.map fun f : R[A] => f.support.inf degt).sum ≤ m.prod.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr <|
    AddMonoidAlgebra.sup_support_multiset_prod_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) m
  · exact degt0
  · exact degtm _ _

