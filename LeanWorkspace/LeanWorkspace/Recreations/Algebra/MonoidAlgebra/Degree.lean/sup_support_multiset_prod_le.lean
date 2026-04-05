import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddCommMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

theorem sup_support_multiset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (m : Multiset R[A]) :
    m.prod.support.sup degb ≤ (m.map fun f : R[A] => f.support.sup degb).sum := by
  induction m using Quot.inductionOn
  rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sum_coe, Multiset.prod_coe]
  exact AddMonoidAlgebra.sup_support_list_prod_le degb0 degbm _

