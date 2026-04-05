import Mathlib

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem affineSpan_coe (s : AffineSubspace k P) : affineSpan k (s : Set P) = s := by
  refine le_antisymm ?_ (subset_affineSpan _ _)
  rintro p ⟨p₁, hp₁, v, hv, rfl⟩
  exact AffineSubspace.vadd_mem_of_mem_direction hv hp₁

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

theorem affineSpan_eq_sInf (s : Set P) :
    affineSpan k s = sInf { s' : AffineSubspace k P | s ⊆ s' } := le_antisymm (affineSpan_le_of_subset_coe <| Set.subset_iInter₂ fun _ => id)
    (sInf_le (subset_spanPoints k _))

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty {s : Set P} (hs : s.Nonempty) :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  refine ⟨AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top k V P, ?_⟩
  intro h
  suffices Nonempty (affineSpan k s) by
    obtain ⟨p, hp : p ∈ affineSpan k s⟩ := this
    rw [AffineSubspace.eq_iff_direction_eq_of_mem hp (AffineSubspace.mem_top k V p), direction_affineSpan, h, AffineSubspace.direction_top]
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨x, mem_affineSpan k hx⟩⟩

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial {s : Set P} [Nontrivial P] :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, subsingleton_iff_bot_eq_top, AddTorsor.subsingleton_iff V P, not_subsingleton]
  · rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty k V P hs]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem card_pos_of_affineSpan_eq_top {ι : Type*} [Fintype ι] {p : ι → P}
    (h : affineSpan k (Set.range p) = ⊤) : 0 < Fintype.card ι := by
  obtain ⟨-, ⟨i, -⟩⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h
  exact Fintype.card_pos_iff.mpr ⟨i⟩

-- An instance with better keys for the context
instance : Nonempty (⊤ : AffineSubspace k P) := inferInstanceAs (Nonempty (⊤ : Set P))

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_direction_eq_vsub_set {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    (s.direction : Set V) = (s : Set P) -ᵥ s := AffineSubspace.directionOfNonempty_eq_direction h ▸ rfl

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_direction_eq_vsub_set_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (p -ᵥ ·) '' s := by
  ext v
  rw [SetLike.mem_coe, ← Submodule.neg_mem_iff, ← SetLike.mem_coe,
    AffineSubspace.coe_direction_eq_vsub_set_right hp, Set.mem_image, Set.mem_image]
  conv_lhs =>
    congr
    ext
    rw [← neg_vsub_eq_vsub_rev, neg_inj]

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_direction_eq_vsub_set_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (· -ᵥ p) '' s := by
  rw [AffineSubspace.coe_direction_eq_vsub_set ⟨p, hp⟩]
  refine le_antisymm ?_ ?_
  · rintro v ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    exact ⟨(p₁ -ᵥ p₂) +ᵥ p,
      AffineSubspace.vadd_mem_of_mem_direction (AffineSubspace.vsub_mem_direction hp₁ hp₂) hp, vadd_vsub _ _⟩
  · rintro v ⟨p₂, hp₂, rfl⟩
    exact ⟨p₂, hp₂, p, hp, rfl⟩

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem coe_eq_bot_iff (Q : AffineSubspace k P) : (Q : Set P) = ∅ ↔ Q = ⊥ := AffineSubspace.coe_injective.eq_iff' (AffineSubspace.bot_coe _ _ _)

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem coe_eq_univ_iff (Q : AffineSubspace k P) : (Q : Set P) = Set.univ ↔ Q = ⊤ := AffineSubspace.coe_injective.eq_iff' (AffineSubspace.top_coe _ _ _)

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem coe_iInf (s : ι → AffineSubspace k P) :
    ((iInf s : AffineSubspace k P) : Set P) = ⋂ i, s i := by
  rw [iInf, AffineSubspace.coe_sInf, Set.biInter_range]

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem directionOfNonempty_eq_direction {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    AffineSubspace.directionOfNonempty h = s.direction := by
  refine le_antisymm ?_ (Submodule.span_le.2 Set.Subset.rfl)
  rw [← SetLike.coe_subset_coe, AffineSubspace.directionOfNonempty, AffineSubspace.direction, Submodule.coe_set_mk,
    AddSubmonoid.coe_set_mk]
  exact vsub_set_subset_vectorSpan k _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    s.direction = ⊤ ↔ s = ⊤ := by
  constructor
  · intro hd
    rw [← AffineSubspace.direction_top k V P] at hd
    refine AffineSubspace.ext_of_direction_eq hd ?_
    simp [h]
  · rintro rfl
    simp

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_iInf (s : ι → AffineSubspace k P) :
    (iInf s).direction ≤ ⨅ i, (s i).direction := by
  apply (AffineSubspace.direction_sInf _).trans_eq
  rw [iInf_range]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_iInf_of_mem (s : ι → AffineSubspace k P) (p : P) (h : ∀ i, p ∈ s i) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf, AffineSubspace.direction_sInf_of_mem _ p ?_, iInf_range]
  rwa [Set.forall_mem_range]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_iInf_of_mem_iInf (s : ι → AffineSubspace k P) (p : P) (h : p ∈ iInf s) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf, AffineSubspace.direction_sInf_of_mem_sInf _ p h, iInf_range]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_inf_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction := by
  ext v
  rw [Submodule.mem_inf, ← AffineSubspace.vadd_mem_iff_mem_direction v h₁, ← AffineSubspace.vadd_mem_iff_mem_direction v h₂, ←
    AffineSubspace.vadd_mem_iff_mem_direction v ((AffineSubspace.mem_inf_iff p s₁ s₂).2 ⟨h₁, h₂⟩), AffineSubspace.mem_inf_iff]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_inf_of_mem_inf {s₁ s₂ : AffineSubspace k P} {p : P} (h : p ∈ s₁ ⊓ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction := AffineSubspace.direction_inf_of_mem ((AffineSubspace.mem_inf_iff p s₁ s₂).1 h).1 ((AffineSubspace.mem_inf_iff p s₁ s₂).1 h).2

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_le {s₁ s₂ : AffineSubspace k P} (h : s₁ ≤ s₂) : s₁.direction ≤ s₂.direction := by
  simp only [AffineSubspace.direction_eq_vectorSpan, vectorSpan_def]
  exact vectorSpan_mono k h

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_sInf_of_mem (t : Set (AffineSubspace k P)) (p : P) (h : ∀ s ∈ t, p ∈ s) :
    AffineSubspace.direction (sInf t) = ⨅ s ∈ t, s.direction := by
  apply (AffineSubspace.direction_sInf t).antisymm
  intro v hv
  rw [← AffineSubspace.vadd_mem_iff_mem_direction v ((AffineSubspace.mem_sInf_iff p t).mpr h), AffineSubspace.mem_sInf_iff]
  intro s hs
  rw [AffineSubspace.vadd_mem_iff_mem_direction v (h s hs)]
  simp only [Submodule.mem_iInf] at hv
  exact hv s hs

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_sInf_of_mem_sInf (t : Set (AffineSubspace k P)) (p : P) (h : p ∈ sInf t) :
    AffineSubspace.direction (sInf t) = ⨅ s ∈ t, s.direction := AffineSubspace.direction_sInf_of_mem t p <| (AffineSubspace.mem_sInf_iff p t).mp h

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem direction_top : (⊤ : AffineSubspace k P).direction = ⊤ := by
  obtain ⟨p⟩ := S.nonempty
  ext v
  refine ⟨imp_intro Submodule.mem_top, fun _hv => ?_⟩
  have hpv : ((v +ᵥ p) -ᵥ p : V) ∈ (⊤ : AffineSubspace k P).direction :=
    AffineSubspace.vsub_mem_direction (AffineSubspace.mem_top k V _) (AffineSubspace.mem_top k V _)
  rwa [vadd_vsub] at hpv

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem eq_bot_or_nonempty (Q : AffineSubspace k P) : Q = ⊥ ∨ (Q : Set P).Nonempty := by
  rw [AffineSubspace.nonempty_iff_ne_bot]
  apply eq_or_ne

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem eq_iff_direction_eq_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁)
    (h₂ : p ∈ s₂) : s₁ = s₂ ↔ s₁.direction = s₂.direction := ⟨fun h => h ▸ rfl, fun h => AffineSubspace.ext_of_direction_eq h ⟨p, h₁, h₂⟩⟩

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : AffineSubspace k P}
    (hd : s₁.direction = s₂.direction) (hn : (s₁ : Set P).Nonempty) (hle : s₁ ≤ s₂) : s₁ = s₂ := let ⟨p, hp⟩ := hn
  AffineSubspace.ext_of_direction_eq hd ⟨p, hp, hle hp⟩

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem ext_of_direction_eq {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
    (hn : ((s₁ : Set P) ∩ s₂).Nonempty) : s₁ = s₂ := by
  ext p
  have hq1 := Set.mem_of_mem_inter_left hn.some_mem
  have hq2 := Set.mem_of_mem_inter_right hn.some_mem
  constructor
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine AffineSubspace.vadd_mem_of_mem_direction ?_ hq2
    rw [← hd]
    exact AffineSubspace.vsub_mem_direction hp hq1
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine AffineSubspace.vadd_mem_of_mem_direction ?_ hq1
    rw [hd]
    exact AffineSubspace.vsub_mem_direction hp hq2

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem inter_eq_singleton_of_nonempty_of_isCompl {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : IsCompl s₁.direction s₂.direction) : ∃ p, (s₁ : Set P) ∩ s₂ = {p} := by
  obtain ⟨p, hp⟩ := AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top
  use p
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq1, hq2⟩
    have hqp : q -ᵥ p ∈ s₁.direction ⊓ s₂.direction :=
      ⟨AffineSubspace.vsub_mem_direction hq1 hp.1, AffineSubspace.vsub_mem_direction hq2 hp.2⟩
    rwa [hd.inf_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hqp
  · exact fun h => h.symm ▸ hp

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem inter_nonempty_of_nonempty_of_sup_direction_eq_top {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : s₁.direction ⊔ s₂.direction = ⊤) : ((s₁ : Set P) ∩ s₂).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hlt := AffineSubspace.sup_direction_lt_of_nonempty_of_inter_empty h1 h2 h
  rw [hd] at hlt
  exact not_top_lt hlt

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem lt_iff_le_and_exists (s₁ s₂ : AffineSubspace k P) :
    s₁ < s₂ ↔ s₁ ≤ s₂ ∧ ∃ p ∈ s₂, p ∉ s₁ := by
  rw [lt_iff_le_not_ge, AffineSubspace.not_le_iff_exists]

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_direction_iff_eq_vsub {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) :
    v ∈ s.direction ↔ ∃ p₁ ∈ s, ∃ p₂ ∈ s, v = p₁ -ᵥ p₂ := by
  rw [← SetLike.mem_coe, AffineSubspace.coe_direction_eq_vsub_set h, Set.mem_vsub]
  simp only [SetLike.mem_coe, eq_comm]

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_direction_iff_eq_vsub_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p -ᵥ p₂ := by
  rw [← SetLike.mem_coe, AffineSubspace.coe_direction_eq_vsub_set_left hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_direction_iff_eq_vsub_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p₂ -ᵥ p := by
  rw [← SetLike.mem_coe, AffineSubspace.coe_direction_eq_vsub_set_right hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem mem_iInf_iff (s : ι → AffineSubspace k P) (p : P) : p ∈ iInf s ↔ ∀ i, p ∈ s i := by
  rw [iInf, AffineSubspace.mem_sInf_iff, Set.forall_mem_range]

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mk'_eq {s : AffineSubspace k P} {p : P} (hp : p ∈ s) : AffineSubspace.mk' p s.direction = s := AffineSubspace.ext_of_direction_eq (AffineSubspace.direction_mk' p s.direction) ⟨p, Set.mem_inter (AffineSubspace.self_mem_mk' _ _) hp⟩

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem nonempty_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [AffineSubspace.span_empty] at h
  exact AffineSubspace.bot_ne_top k V P h

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem spanPoints_subset_coe_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s ⊆ s₁) :
    spanPoints k s ⊆ s₁ := by
  rintro p ⟨p₁, hp₁, v, hv, hp⟩
  rw [hp]
  have hp₁s₁ : p₁ ∈ (s₁ : Set P) := Set.mem_of_mem_of_subset hp₁ h
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ hp₁s₁
  have hs : vectorSpan k s ≤ s₁.direction := vectorSpan_mono k h
  rw [SetLike.le_def] at hs
  rw [← SetLike.mem_coe]
  exact Set.mem_of_mem_of_subset hv hs

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

theorem span_iUnion {ι : Type*} (s : ι → Set P) :
    affineSpan k (⋃ i, s i) = ⨆ i, affineSpan k (s i) := (AffineSubspace.gi k V P).gc.l_iSup

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

theorem span_univ : affineSpan k (Set.univ : Set P) = ⊤ := eq_top_iff.2 <| subset_affineSpan k _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem sup_direction_lt_of_nonempty_of_inter_empty {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (he : (s₁ ∩ s₂ : Set P) = ∅) :
    s₁.direction ⊔ s₂.direction < (s₁ ⊔ s₂).direction := by
  obtain ⟨p₁, hp₁⟩ := h1
  obtain ⟨p₂, hp₂⟩ := h2
  rw [SetLike.lt_iff_le_and_exists]
  use AffineSubspace.sup_direction_le s₁ s₂, p₂ -ᵥ p₁,
    AffineSubspace.vsub_mem_direction ((le_sup_right : s₂ ≤ s₁ ⊔ s₂) hp₂) ((le_sup_left : s₁ ≤ s₁ ⊔ s₂) hp₁)
  intro h
  rw [Submodule.mem_sup] at h
  rcases h with ⟨v₁, hv₁, v₂, hv₂, hv₁v₂⟩
  rw [← sub_eq_zero, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm v₁, add_assoc, ←
    vadd_vsub_assoc, ← neg_neg v₂, add_comm, ← sub_eq_add_neg, ← vsub_vadd_eq_vsub_sub,
    vsub_eq_zero_iff_eq] at hv₁v₂
  refine Set.Nonempty.ne_empty ?_ he
  use v₁ +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv₁ hp₁
  rw [hv₁v₂]
  exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv₂) hp₂

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_iff_mem_direction {s : AffineSubspace k P} (v : V) {p : P} (hp : p ∈ s) :
    v +ᵥ p ∈ s ↔ v ∈ s.direction := ⟨fun h => by simpa using AffineSubspace.vsub_mem_direction h hp, fun h => AffineSubspace.vadd_mem_of_mem_direction h hp⟩

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_iff_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction)
    {p : P} : v +ᵥ p ∈ s ↔ p ∈ s := by
  refine ⟨fun h => ?_, fun h => AffineSubspace.vadd_mem_of_mem_direction hv h⟩
  convert AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) h
  simp

end

section

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction) {p : P}
    (hp : p ∈ s) : v +ᵥ p ∈ s := by
  rw [AffineSubspace.mem_direction_iff_eq_vsub ⟨p, hp⟩] at hv
  rcases hv with ⟨p₁, hp₁, p₂, hp₂, hv⟩
  rw [hv]
  convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp
  rw [one_smul]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem vectorSpan_eq_top_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) :
    vectorSpan k s = ⊤ := by rw [← direction_affineSpan, h, AffineSubspace.direction_top]

end
