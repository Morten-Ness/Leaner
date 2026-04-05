import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_subtype_mul_prod_subtype (p : ι → Prop) (f : ι → M) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s, ← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]

