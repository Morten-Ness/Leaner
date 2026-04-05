import Mathlib

variable {M N γ : Type*}

variable {ι : Type*}

theorem prod_smul
    [CommMonoid N] [CommMonoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : ι → M) (f : ι → N) :
    ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

