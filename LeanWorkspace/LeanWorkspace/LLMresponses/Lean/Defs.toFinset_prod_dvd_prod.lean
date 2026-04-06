FAIL
import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [DecidableEq α]

theorem toFinset_prod_dvd_prod [DecidableEq M] [CommMonoid M] (S : Multiset M) :
    S.toFinset.prod id ∣ S.prod := by
  classical
  induction S using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      by_cases h : a ∈ s
      · rw [Multiset.toFinset_cons_of_mem h, Multiset.prod_cons]
        rcases ih with ⟨c, hc⟩
        refine ⟨a * c, ?_⟩
        rw [hc]
        ac_rfl
      · rw [Multiset.toFinset_cons_of_not_mem h, Multiset.prod_cons]
        rcases ih with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        rw [Finset.prod_insert]
        · rw [hc]
          ac_rfl
        · simpa [Multiset.mem_toFinset] using h
