import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_attach_eq_prod_dite [Fintype ι] (s : Finset ι) (f : s → M) [DecidablePred (· ∈ s)] :
    ∏ i ∈ s.attach, f i = ∏ i, if h : i ∈ s then f ⟨i, h⟩ else 1 := by
  rw [Finset.prod_dite, Finset.univ_eq_attach, Finset.prod_const_one, mul_one]
  congr
  · simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

