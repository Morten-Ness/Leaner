import Mathlib

variable {η : Type*} {f : η → Type*} [∀ i, MulOneClass (f i)]

variable {S : Type*} [SetLike S (Π i, f i)] [SubmonoidClass S (Π i, f i)]

theorem pi_le_iff [Finite η] [DecidableEq η] {H : Π i, Submonoid (f i)} {J : Submonoid (Π i, f i)} :
    pi Set.univ H ≤ J ↔ ∀ i : η, map (MonoidHom.mulSingle f i) (H i) ≤ J := ⟨fun h i _ ⟨x, hx, H⟩ => h <| by simpa [← H],
   fun h x hx => Submonoid.pi_mem_of_mulSingle_mem x fun i => h i (mem_map_of_mem _ (hx i trivial))⟩

