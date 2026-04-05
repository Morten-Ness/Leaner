import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : ∀ x ∈ m, x ∈ S) :
    m.noncommProd comm ∈ S := by
  induction m using Quotient.inductionOn with | h l => ?_
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  exact Submonoid.list_prod_mem _ h

