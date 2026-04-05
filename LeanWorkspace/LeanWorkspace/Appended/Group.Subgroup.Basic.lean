import Mathlib

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.comap {H : Subgroup N} (hH : H.Normal) (f : G →* N) : (H.comap f).Normal := ⟨fun _ => by simp +contextual [Subgroup.mem_comap, hH.conj_mem]⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

theorem Normal.map {H : Subgroup G} (h : H.Normal) (f : G →* N) (hf : Function.Surjective f) :
    (H.map f).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← f.range_eq_top_of_surjective hf, f.range_eq_map,
    ← H.normalizer_eq_top]
  exact Subgroup.le_normalizer_map _

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.of_map_injective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {L : Subgroup G} (n : (L.map φ).Normal) : L.Normal := L.comap_map_eq_self_of_injective hφ ▸ n.comap φ

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.of_map_subtype {K : Subgroup G} {L : Subgroup K}
    (n : (Subgroup.map K.subtype L).Normal) : L.Normal := n.of_map_injective K.subtype_injective

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem SubgroupNormal.mem_comm {H K : Subgroup G} (hK : H ≤ K) [hN : (H.subgroupOf K).Normal]
    {a b : G} (hb : b ∈ K) (h : a * b ∈ H) : b * a ∈ H := by
  have := (Subgroup.normal_subgroupOf_iff hK).mp hN (a * b) b h hb
  rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥ := SetLike.coe_injective <| by simp [Subgroup.coe_prod]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem characteristic_iff_comap_le : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom ≤ H := Subgroup.characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => le_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (h ϕ) fun g hg => h ϕ.symm ((congr_arg (· ∈ H) (ϕ.symm_apply_apply g)).mpr hg)⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem characteristic_iff_le_comap : H.Characteristic ↔ ∀ ϕ : G ≃* G, H ≤ H.comap ϕ.toMonoidHom := Subgroup.characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => ge_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (fun g hg => (congr_arg (· ∈ H) (ϕ.symm_apply_apply g)).mp (h ϕ.symm hg)) (h ϕ)⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem commute_of_normal_of_disjoint (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ : H₂.Normal)
    (hdis : Disjoint H₁ H₂) (x y : G) (hx : x ∈ H₁) (hy : y ∈ H₂) : Commute x y := by
  suffices x * y * x⁻¹ * y⁻¹ = 1 by
    change x * y = y * x
    · rw [mul_assoc, mul_eq_one_iff_eq_inv] at this
      simpa
  apply hdis.le_bot
  constructor
  · suffices x * (y * x⁻¹ * y⁻¹) ∈ H₁ by simpa [mul_assoc]
    exact H₁.mul_mem hx (hH₁.conj_mem _ (H₁.inv_mem hx) _)
  · change x * y * x⁻¹ * y⁻¹ ∈ H₂
    apply H₂.mul_mem _ (H₂.inv_mem hy)
    apply hH₂.conj_mem _ hy

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conj_mem_conjugatesOfSet {x c : G} :
    x ∈ Group.conjugatesOfSet s → c * x * c⁻¹ ∈ Group.conjugatesOfSet s := fun H => by
  rcases Group.mem_conjugatesOfSet_iff.1 H with ⟨a, h₁, h₂⟩
  exact Group.mem_conjugatesOfSet_iff.2 ⟨a, h₁, h₂.trans (isConj_iff.2 ⟨c, rfl⟩)⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conjugatesOfSet_subset {s : Set G} {N : Subgroup G} [N.Normal] (h : s ⊆ N) :
    Group.conjugatesOfSet s ⊆ N := Set.iUnion₂_subset fun _x H => Group.conjugates_subset_normal (h H)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conjugates_subset_normal {N : Subgroup G} [tn : N.Normal] {a : G} (h : a ∈ N) :
    conjugatesOf a ⊆ N := by
  rintro a hc
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact tn.conj_mem a h c

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (h : G₂ →* G₃) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem inf_subgroupOf_inf_normal_of_left {A' A : Subgroup G} (B : Subgroup G)
    [hN : (A'.subgroupOf A).Normal] : ((A' ⊓ B).subgroupOf (A ⊓ B)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm, inf_idem]
  exact le_trans (inf_le_inf hN B.le_normalizer) Subgroup.inf_normalizer_le_normalizer_inf

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem inf_subgroupOf_inf_normal_of_right (A B' B : Subgroup G)
    [hN : (B'.subgroupOf B).Normal] : ((A ⊓ B').subgroupOf (A ⊓ B)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm, inf_idem]
  exact le_trans (inf_le_inf A.le_normalizer hN) Subgroup.inf_normalizer_le_normalizer_inf

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem le_normalClosure {H : Subgroup G} : H ≤ Subgroup.normalClosure ↑H := fun _ h =>
  Subgroup.subset_normalClosure h

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (x : G₁) : (f.liftOfRightInverseAux f_inv hf g hg) (f x) = g x := by
  dsimp [MonoidHom.liftOfRightInverseAux]
  rw [← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
  apply hg
  rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one]
  simp only [hf _]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) : (f.liftOfRightInverse f_inv hf g).comp f = g := MonoidHom.ext <| MonoidHom.liftOfRightInverse_comp_apply f f_inv hf g

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) (x : G₁) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x := MonoidHom.liftOfRightInverseAux_comp_apply f f_inv hf g.1 g.2 x

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem mem_conjugatesOfSet_iff {x : G} : x ∈ Group.conjugatesOfSet s ↔ ∃ a ∈ s, IsConj a x := by
  rw [Group.conjugatesOfSet, Set.mem_iUnion₂]
  simp only [conjugatesOf, isConj_iff, Set.mem_setOf_eq, exists_prop]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

theorem mulSingle_mem_pi [DecidableEq η] {I : Set η} {H : ∀ i, Subgroup (f i)} (i : η) (x : f i) :
    Pi.mulSingle i x ∈ Subgroup.pi I H ↔ i ∈ I → x ∈ H i := Set.update_mem_pi_iff_of_mem (one_mem (Subgroup.pi I H))

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_eq_self (H : Subgroup G) [H.Normal] : Subgroup.normalClosure ↑H = H := le_antisymm (Subgroup.normalClosure_le_normal rfl.subset) Subgroup.le_normalClosure

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_mono {s t : Set G} (h : s ⊆ t) : Subgroup.normalClosure s ≤ Subgroup.normalClosure t := Subgroup.normalClosure_le_normal (Set.Subset.trans h Subgroup.subset_normalClosure)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_subset_iff {N : Subgroup G} [N.Normal] : s ⊆ N ↔ Subgroup.normalClosure s ≤ N := ⟨Subgroup.normalClosure_le_normal, Set.Subset.trans Subgroup.subset_normalClosure⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_eq_self (H : Subgroup G) [H.Normal] : H.normalCore = H := le_antisymm H.normalCore_le (Subgroup.normal_le_normalCore.mpr le_rfl)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_le (H : Subgroup G) : H.normalCore ≤ H := fun a h => by
  rw [← mul_one a, ← inv_one, ← one_mul a]
  exact h 1

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_mono {H K : Subgroup G} (h : H ≤ K) : H.normalCore ≤ K.normalCore := Subgroup.normal_le_normalCore.mpr (H.normalCore_le.trans h)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem normal_iInf_normal {ι : Sort*} {a : ι → Subgroup G}
    (norm : ∀ i : ι, (a i).Normal) : (iInf a).Normal := by
  constructor
  intro g g_in_iInf h
  rw [Subgroup.mem_iInf] at g_in_iInf ⊢
  intro i
  exact (norm i).conj_mem g (g_in_iInf i) h

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normal_le_normalCore {H : Subgroup G} {N : Subgroup G} [hN : N.Normal] :
    N ≤ H.normalCore ↔ N ≤ H := ⟨ge_trans H.normalCore_le, fun h_le n hn g => h_le (hN.conj_mem n hn g)⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem normal_subgroupOf_iff {H K : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K).Normal ↔ ∀ h k, h ∈ H → k ∈ K → k * h * k⁻¹ ∈ H := ⟨fun hN h k hH hK => hN.conj_mem ⟨h, hHK hH⟩ hH ⟨k, hK⟩, fun hN =>
    { conj_mem := fun h hm k => hN h.1 k.1 hm k.2 }⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

theorem pi_eq_bot_iff (H : ∀ i, Subgroup (f i)) : Subgroup.pi Set.univ H = ⊥ ↔ ∀ i, H i = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_eq_bot_iff {H : Subgroup G} {K : Subgroup N} : H.prod K = ⊥ ↔ H = ⊥ ∧ K = ⊥ := by
  simpa only [← Subgroup.toSubmonoid_inj] using Submonoid.prod_eq_bot_iff

end

section

open scoped Int Relator

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_mono : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) (@Subgroup.prod G _ N _) (@Subgroup.prod G _ N _) := fun _s _s' hs _t _t' ht => Set.prod_mono hs ht

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_mono_left (H : Subgroup N) : Monotone fun K : Subgroup G => K.prod H := fun _ _ hs =>
  Subgroup.prod_mono hs (le_refl H)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem subset_conjugatesOfSet : s ⊆ Group.conjugatesOfSet s := fun (x : G) (h : x ∈ s) =>
  Group.mem_conjugatesOfSet_iff.2 ⟨x, h, IsConj.refl _⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem subset_normalClosure : s ⊆ Subgroup.normalClosure s := Set.Subset.trans Group.subset_conjugatesOfSet Subgroup.conjugatesOfSet_subset_normalClosure

end
