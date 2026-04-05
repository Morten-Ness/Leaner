import Mathlib

variable {η : Type*} {f : η → Type*} [∀ i, MulOneClass (f i)]

variable {S : Type*} [SetLike S (Π i, f i)] [SubmonoidClass S (Π i, f i)]

theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : S} (x : Π i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H := by
  cases nonempty_fintype η
  exact Submonoid.pi_mem_of_mulSingle_mem_aux Finset.univ x (by simp) fun i _ => h i

