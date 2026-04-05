import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [Semiring R]

variable [AddMonoid A] [AddMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

theorem le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (n : ℕ) (f : R[A]) : n • f.support.inf degt ≤ (f ^ n).support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr <| AddMonoidAlgebra.sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) n f
  · exact degt0
  · exact degtm _ _

