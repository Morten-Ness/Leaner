import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

theorem induction {p : SkewMonoidAlgebra M α → Prop} (f : SkewMonoidAlgebra M α) (h0 : p 0)
    (ha : ∀ (a b) (f : SkewMonoidAlgebra M α), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
    p f := suffices ∀ (s) (f : SkewMonoidAlgebra M α), f.support = s → p f from this _ _ rfl
  fun s ↦
  Finset.cons_induction_on s (fun f hf ↦ by rwa [support_eq_empty.1 hf]) fun a s has ih f hf ↦ by
    suffices p (single a (f.coeff a) + f.erase a) by rwa [SkewMonoidAlgebra.single_add_erase] at this
    classical
    apply ha
    · rw [SkewMonoidAlgebra.support_erase, Finset.mem_erase]
      exact fun H ↦ H.1 rfl
    · simp only [← mem_support_iff, hf, Finset.mem_cons_self]
    · apply ih
      rw [SkewMonoidAlgebra.support_erase, hf, Finset.erase_cons]

