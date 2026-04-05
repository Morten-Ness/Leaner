import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

theorem closure_pi [Finite η] {s : Π i, Set (f i)} (hs : ∀ i, 1 ∈ s i) :
    closure (Set.univ.pi fun i => s i) = pi Set.univ fun i => closure (s i) := le_antisymm
    ((closure_le _).2 <| pi_subset_pi_iff.2 <| .inl fun _ _ => subset_closure)
    (by
      classical
      exact Subgroup.pi_le_iff.mpr fun i => (gc_map_comap _).l_le <| (closure_le _).2 fun _x hx =>
          subset_closure <| mem_univ_pi.mpr fun j => by
        by_cases H : j = i
        · subst H
          simpa
        · simpa [H] using hs _)

