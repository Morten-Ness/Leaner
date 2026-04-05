import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

theorem mem_finsuppAntidiag_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι →₀ μ} :
    f ∈ Finset.finsuppAntidiag (insert a s) n ↔
      ∃ m ∈ antidiagonal n, ∃ (g : ι →₀ μ),
        f = Finsupp.update g a m.1 ∧ g ∈ Finset.finsuppAntidiag s m.2 := by
  simp only [mem_finsuppAntidiag, mem_antidiagonal, Prod.exists, sum_insert h]
  constructor
  · rintro ⟨rfl, hsupp⟩
    refine ⟨_, _, rfl, Finsupp.erase a f, ?_, ?_, ?_⟩
    · rw [update_erase_eq_update, Finsupp.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hx h)]
    · rwa [support_erase, ← subset_insert_iff]
  · rintro ⟨n1, n2, rfl, g, rfl, rfl, hgsupp⟩
    refine ⟨?_, (support_update_subset _ _).trans (insert_subset_insert a hgsupp)⟩
    simp only [coe_update]
    apply congr_arg₂
    · rw [Function.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [update_of_ne (ne_of_mem_of_not_mem hx h) n1 ⇑g]

