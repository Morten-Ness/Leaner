import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddCommMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

theorem sup_support_finset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (s : Finset ι) (f : ι → R[A]) :
    (∏ i ∈ s, f i).support.sup degb ≤ ∑ i ∈ s, (f i).support.sup degb := (AddMonoidAlgebra.sup_support_multiset_prod_le degb0 degbm _).trans_eq <| congr_arg _ <| Multiset.map_map _ _ _

