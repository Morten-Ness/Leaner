FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_subtype_mul_prod_subtype (p : ι → Prop) (f : ι → M) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
  let e : ({ x // p x } ⊕ { x // ¬ p x }) ≃ ι :=
    Equiv.sumCompl (p := p)
  calc
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i
        = ∏ x : ({ x // p x } ⊕ { x // ¬ p x }),
            f (e x) := by
          rw [Fintype.prod_sum_type]
          rfl
    _ = ∏ i : ι, f i := by
      symm
      exact Fintype.prod_equiv e.symm (fun x => f x) (by intro x; rfl)
