import Mathlib

variable {η : Type*} {f : η → Type*} [∀ i, MulOneClass (f i)]

variable {S : Type*} [SetLike S (Π i, f i)] [SubmonoidClass S (Π i, f i)]

theorem closure_pi [Finite η] {s : Π i, Set (f i)} (hs : ∀ i, 1 ∈ s i) :
    closure (Set.univ.pi fun i => s i) = pi Set.univ fun i => closure (s i) := le_antisymm
    (closure_le.2 <| pi_subset_pi_iff.2 <| .inl fun _ _ => subset_closure)
    (by
      classical
      exact Submonoid.pi_le_iff.mpr fun i => map_le_of_le_comap _ <| closure_le.2 fun _x hx =>
          subset_closure <| mem_univ_pi.mpr fun j => by
        by_cases H : j = i
        · subst H
          simpa
        · simpa [H] using hs _)

