FAIL
import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

theorem hasFiniteSupport (A : ι → S) (x : DirectSum ι fun i => A i) :
    (fun i => (x i : M)).HasFiniteSupport := by
  classical
  rw [Function.HasFiniteSupport]
  classical
  let s : Set ι := {i | x i ≠ 0}
  have hs : s.Finite := by
    classical
    simpa [s, DFinsupp.support, Set.toFinset_setOf, Ne.def] using (x.support.finite_toSet)
  simpa [s, Function.support, Ne.def] using hs
