FAIL
import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : ∀ x ∈ m, x ∈ S) :
    m.noncommProd comm ∈ S := by
  classical
  rcases Quot.exists_rep m with ⟨l, rfl⟩
  induction l with
  | nil =>
      simpa using S.one_mem
  | cons a t ih =>
      have ha : a ∈ S := h a (by simp)
      have ht : ∀ x ∈ t, x ∈ S := by
        intro x hx
        exact h x (by simp [hx])
      simpa [Multiset.noncommProd_coe] using S.mul_mem ha (ih ht)
