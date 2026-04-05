import Mathlib

section

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

theorem coe_finset_prod {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι → S)
    (s : Finset ι) : ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M) := map_prod (SubmonoidClass.subtype S) f s

end

section

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

theorem coe_list_prod (l : List S) : (l.prod : M) = (l.map (↑)).prod := map_list_prod (SubmonoidClass.subtype S : _ →* M) l

end

section

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod := (SubmonoidClass.subtype S : _ →* M).map_multiset_prod m

end

section

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : ∀ x ∈ m, x ∈ S) :
    m.noncommProd comm ∈ S := by
  induction m using Quotient.inductionOn with | h l => ?_
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  exact Submonoid.list_prod_mem _ h

end

section

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem noncommProd_mem (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι → M) (comm)
    (h : ∀ c ∈ t, f c ∈ S) : t.noncommProd f comm ∈ S := by
  apply Submonoid.multiset_noncommProd_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

end
