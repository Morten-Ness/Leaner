import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {q : Submodule R M} {m : M}

theorem aeval_apply_smul_mem_of_le_comap
    (hm : m ∈ q) (p : R[X]) (f : Module.End R M) (hq : q ≤ q.comap f) :
    Polynomial.aeval f p m ∈ q := Polynomial.aeval_apply_smul_mem_of_le_comap' hm p f hq

