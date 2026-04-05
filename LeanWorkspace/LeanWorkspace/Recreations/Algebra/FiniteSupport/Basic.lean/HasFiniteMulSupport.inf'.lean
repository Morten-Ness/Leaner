import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.inf' [SemilatticeInf M] {ι : Type*} {f : ι → α → M}
    (s : Finset ι) (hf : ∀ i ∈ s, HasFiniteMulSupport (f i)) (hs : s.Nonempty) :
    HasFiniteMulSupport fun a ↦ s.inf' hs (f · a) := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (s.finite_toSet.biUnion hf).subset fun a ha ↦ ?_
  simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at ha ⊢
  contrapose! ha
  exact Finset.inf'_eq_of_forall hs (fun x ↦ f x a) ha

