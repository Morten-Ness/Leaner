import Mathlib

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem bot_subgroupOf : (⊥ : Subgroup G).subgroupOf H = ⊥ := Eq.symm (Subgroup.ext fun _g => Subtype.ext_iff)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem codisjoint_map {f : G →* N} (hf : Function.Surjective f)
    {H K : Subgroup G} (h : Codisjoint H K) : Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff, ← Subgroup.map_sup, codisjoint_iff.mp h, Subgroup.map_top_of_surjective _ hf]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_equiv_eq_map_symm' (f : N ≃* G) (K : Subgroup G) :
    K.comap f.toMonoidHom = K.map f.symm.toMonoidHom := (Subgroup.map_equiv_eq_comap_symm f.symm K).symm

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_equiv_eq_map_symm (f : N ≃* G) (K : Subgroup G) :
    K.comap (G := N) f = K.map f.symm :=
  (Subgroup.map_equiv_eq_comap_symm f.symm K).symm

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_sup_comap_le (H K : Subgroup N) (f : G →* N) :
    Subgroup.comap f H ⊔ Subgroup.comap f K ≤ Subgroup.comap f (H ⊔ K) := Monotone.le_map_sup (fun _ _ => Subgroup.comap_mono) H K

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem disjoint_map {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff, ← Subgroup.map_inf _ _ f hf, disjoint_iff.mp h, Subgroup.map_bot]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem gc_map_comap (f : G →* N) : GaloisConnection (Subgroup.map f) (Subgroup.comap f) := fun _ _ =>
  Subgroup.map_le_iff_le_comap

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem iSup_comap_le {ι : Sort*} (f : G →* N) (s : ι → Subgroup N) :
    ⨆ i, (s i).comap f ≤ (iSup s).comap f := Monotone.le_map_iSup fun _ _ => Subgroup.comap_mono

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem inf_subgroupOf_left (H K : Subgroup G) : (K ⊓ H).subgroupOf K = H.subgroupOf K := by
  rw [inf_comm, Subgroup.inf_subgroupOf_right]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem inf_subgroupOf_right (H K : Subgroup G) : (H ⊓ K).subgroupOf K = H.subgroupOf K := Subgroup.subgroupOf_inj.2 (inf_right_idem _ _)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem map_eq_comap_of_inverse {f : G →* N} {g : N →* G} (hl : Function.LeftInverse g f)
    (hr : Function.RightInverse g f) (H : Subgroup G) : Subgroup.map f H = Subgroup.comap g H := SetLike.ext' <| by rw [Subgroup.coe_map, Subgroup.coe_comap, Set.image_eq_preimage_of_inverse hl hr]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_equiv_eq_comap_symm' (f : G ≃* N) (K : Subgroup G) :
    K.map f.toMonoidHom = K.comap f.symm.toMonoidHom := SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_equiv_eq_comap_symm (f : G ≃* N) (K : Subgroup G) :
    K.map f = K.comap (G := N) f.symm :=
  Subgroup.map_equiv_eq_comap_symm' _ _

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_equiv_top {F : Type*} [EquivLike F G N] [MulEquivClass F G N] (f : F) :
    Subgroup.map (f : G →* N) ⊤ = ⊤ := Subgroup.map_top_of_surjective _ (EquivLike.surjective f)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    (H ⊓ K).map f = H.map f ⊓ K.map f := SetLike.coe_injective (Set.image_inter hf)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf_eq (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    Subgroup.map f (H ⊓ K) = Subgroup.map f H ⊓ Subgroup.map f K := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf_le (H K : Subgroup G) (f : G →* N) : Subgroup.map f (H ⊓ K) ≤ Subgroup.map f H ⊓ Subgroup.map f K := le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_one_eq_bot : K.map (1 : G →* N) = ⊥ := eq_bot_iff.mpr <| by
    rintro x ⟨y, _, rfl⟩
    simp

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_subgroupOf_eq_of_le {H K : Subgroup G} (h : H ≤ K) :
    (H.subgroupOf K).map K.subtype = H := by
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_symm_eq_iff_map_eq {H : Subgroup N} {e : G ≃* N} :
    H.map ↑e.symm = K ↔ K.map ↑e = H := by
  constructor <;> rintro rfl
  · rw [Subgroup.map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
      MulEquiv.coe_monoidHom_refl, Subgroup.map_id]
  · rw [Subgroup.map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
      MulEquiv.coe_monoidHom_refl, Subgroup.map_id]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_top_of_surjective (f : G →* N) (h : Function.Surjective f) : Subgroup.map f ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, trivial, hy⟩

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K := Set.mem_image_equiv

-- The simpNF linter says that the LHS can be simplified via `Subgroup.mem_map`.
-- However this is a higher priority lemma.
-- It seems the side condition `hf` is not applied by `simpNF`.
-- https://github.com/leanprover/std4/issues/207

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem mem_subgroupOf {H K : Subgroup G} {h : K} : h ∈ H.subgroupOf K ↔ (h : G) ∈ H := Iff.rfl

-- TODO(kmill): use `K ⊓ H` order for RHS to match `Subtype.image_preimage_coe`

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem subgroupComap_surjective_of_surjective (f : G →* G') (H' : Subgroup G') (hf : Function.Surjective f) :
    Function.Surjective (f.subgroupComap H') := f.submonoidComap_surjective_of_surjective H'.toSubmonoid hf

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem subgroupMap_surjective (f : G →* G') (H : Subgroup G) :
    Function.Surjective (f.subgroupMap H) := f.submonoidMap_surjective H.toSubmonoid

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_eq_bot {H K : Subgroup G} : H.subgroupOf K = ⊥ ↔ Disjoint H K := by
  rw [disjoint_iff, ← Subgroup.bot_subgroupOf, Subgroup.subgroupOf_inj, bot_inf_eq]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_eq_top {H K : Subgroup G} : H.subgroupOf K = ⊤ ↔ K ≤ H := by
  rw [← Subgroup.top_subgroupOf, Subgroup.subgroupOf_inj, top_inf_eq, inf_eq_right]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_map_subtype (H K : Subgroup G) : (H.subgroupOf K).map K.subtype = H ⊓ K := SetLike.ext' <| by refine Subtype.image_preimage_coe _ _ |>.trans ?_; apply Set.inter_comm

end
