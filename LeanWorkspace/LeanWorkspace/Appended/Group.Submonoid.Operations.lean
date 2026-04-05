import Mathlib

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1 : M) := S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  simp only [Submonoid.eq_bot_iff_forall, Submonoid.nontrivial_iff_exists_ne_one, ← not_forall, ← Classical.not_imp,
    Classical.em]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥ := SetLike.coe_injective <| by simp [Submonoid.coe_prod]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem codisjoint_map {F : Type*} [FunLike F M N] [MonoidHomClass F M N] {f : F}
    (hf : Function.Surjective f) {H K : Submonoid M} (h : Codisjoint H K) :
    Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff, ← Submonoid.map_sup, codisjoint_iff.mp h, ← MonoidHom.mrange_eq_map,
    MonoidHom.mrange_eq_top_of_surjective _ hf]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) :
    K.comap f = K.map f.symm := (Submonoid.map_equiv_eq_comap_symm f.symm K).symm

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem comap_iInf {ι : Sort*} (f : F) (s : ι → Submonoid N) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (Submonoid.gc_map_comap f : GaloisConnection (Submonoid.map f) (Submonoid.comap f)).u_iInf

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem comap_inf (S T : Submonoid N) (f : F) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f := (Submonoid.gc_map_comap f : GaloisConnection (Submonoid.map f) (Submonoid.comap f)).u_inf

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f := (Submonoid.gc_map_comap f).u_l_u_eq_u _

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem disjoint_map {f : F} (hf : Function.Injective f) {H K : Submonoid M} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff, ← Submonoid.map_inf _ _ f hf, disjoint_iff.mp h, Submonoid.map_bot]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem eq_bot_iff_forall : S = ⊥ ↔ ∀ x ∈ S, x = (1 : M) := SetLike.ext_iff.trans <| by simp +contextual [iff_def, S.one_mem]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem eq_bot_of_subsingleton [Subsingleton S] : S = ⊥ := by
  rw [Submonoid.eq_bot_iff_forall]
  intro y hy
  simpa using congr_arg ((↑) : S → M) <| Subsingleton.elim (⟨y, hy⟩ : S) 1

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem gc_map_comap (f : F) : GaloisConnection (Submonoid.map f) (Submonoid.comap f) := fun _ _ => Submonoid.map_le_iff_le_comap

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem iSup_map_mulSingle_le [DecidableEq ι] {I : Set ι} {S : ∀ i, Submonoid (M i)} :
    ⨆ i, Submonoid.map (MonoidHom.mulSingle M i) (S i) ≤ Submonoid.pi I S := iSup_le fun _ => Submonoid.map_le_iff_le_comap.mpr (Submonoid.le_comap_mulSingle_pi _)

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem inclusion_inj {S T : Submonoid M} (h : S ≤ T) {x y : S} :
    Submonoid.inclusion h x = Submonoid.inclusion h y ↔ x = y := (Submonoid.inclusion_injective h).eq_iff

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem injective_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S)
    (h : ∀ x, f x ∈ s) : Function.Injective (f.codRestrict s h) ↔ Function.Injective f := ⟨fun H _ _ hxy ↦ H <| Subtype.ext hxy, fun H _ _ hxy ↦ H (congr_arg Subtype.val hxy)⟩

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem le_comap_map {f : F} : S ≤ (S.map f).comap f := (Submonoid.gc_map_comap f).le_u_l _

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_eq (f : F) (S : Submonoid N) : (S.comap f).map f = S ⊓ MonoidHom.mrange f := SetLike.coe_injective Set.image_preimage_eq_inter_range

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_eq_self {f : F} {S : Submonoid N} (h : S ≤ MonoidHom.mrange f) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using Submonoid.map_comap_eq f S

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_eq_self_of_surjective {f : F} (h : Function.Surjective f) {S : Submonoid N} :
    Submonoid.map f (Submonoid.comap f S) = S := Submonoid.map_comap_eq_self (MonoidHom.mrange_eq_top_of_surjective _ h ▸ le_top)

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f ≤ S := (Submonoid.gc_map_comap f).l_u_le _

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f := (Submonoid.gc_map_comap f).l_u_l_eq_l _

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) :
    K.map f = K.comap f.symm := SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f = ⊤ := SetLike.coe_injective <| Set.image_univ.trans f.surjective.range_eq

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_inf (S T : Submonoid M) (f : F) (hf : Function.Injective f) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f = S.map f ⊔ T.map f := (Submonoid.gc_map_comap f : GaloisConnection (Submonoid.map f) (Submonoid.comap f)).l_sup

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mker_one : MonoidHom.mker (1 : M →* N) = ⊤ := by
  ext
  simp [MonoidHom.mem_mker]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem monotone_comap {f : F} : Monotone (Submonoid.comap f) := (Submonoid.gc_map_comap f).monotone_u

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem monotone_map {f : F} : Monotone (Submonoid.map f) := (Submonoid.gc_map_comap f).monotone_l

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrangeRestrict_mker (f : M →* N) : MonoidHom.mker (MonoidHom.mrangeRestrict f) = MonoidHom.mker f := by
  ext x
  change (⟨f x, _⟩ : MonoidHom.mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrange_comp {O : Type*} [MulOneClass O] (f : N →* O) (g : M →* N) :
    MonoidHom.mrange (f.comp g) = (MonoidHom.mrange g).map f := SetLike.coe_injective <| Set.range_comp f _

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrange_id : MonoidHom.mrange (MonoidHom.id M) = ⊤ := by
  simp [MonoidHom.mrange_eq_map]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem mrange_subtype (s : Submonoid M) : MonoidHom.mrange s.subtype = s := SetLike.coe_injective <| (MonoidHom.coe_mrange _).trans <| Subtype.range_coe

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem mulSingle_mem_pi [DecidableEq ι] {I : Set ι} {S : ∀ i, Submonoid (M i)} (i : ι) (x : M i) :
    Pi.mulSingle i x ∈ Submonoid.pi I S ↔ i ∈ I → x ∈ S i := Set.update_mem_pi_iff_of_mem (one_mem (Submonoid.pi I _))

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ ∃ x ∈ S, x ≠ (1 : M) := calc
    Nontrivial S ↔ ∃ x : S, x ≠ 1 := nontrivial_iff_exists_ne 1
    _ ↔ ∃ (x : _) (hx : x ∈ S), (⟨x, hx⟩ : S) ≠ ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ ∃ x ∈ S, x ≠ (1 : M) := by simp [Ne]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem pi_eq_bot_iff (S : ∀ i, Submonoid (M i)) : Submonoid.pi Set.univ S = ⊥ ↔ ∀ i, S i = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) :
    (Submonoid.prod s ⊥) ⊔ (Submonoid.prod ⊥ t) = Submonoid.prod s t := (le_antisymm (sup_le (Submonoid.prod_mono (le_refl s) bot_le) (Submonoid.prod_mono bot_le (le_refl t))))
    fun p hp => Prod.fst_mul_snd p ▸ mul_mem
        ((le_sup_left : Submonoid.prod s ⊥ ≤ Submonoid.prod s ⊥ ⊔ Submonoid.prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : Submonoid.prod ⊥ t ≤ Submonoid.prod s ⊥ ⊔ Submonoid.prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  simp only [eq_bot_iff, Submonoid.prod_le_iff, (Submonoid.gc_map_comap _).le_iff_le, MonoidHom.comap_bot', MonoidHom.mker_inl, MonoidHom.mker_inr]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, Submonoid.le_prod_iff, ← MonoidHom.mrange_eq_map, Submonoid.mrange_fst, Submonoid.mrange_snd]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem submonoidComap_surjective_of_surjective (f : M →* N) (N' : Submonoid N) (hf : Function.Surjective f) :
    Function.Surjective (f.submonoidComap N') := fun y ↦ by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, Submonoid.mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem submonoidMap_surjective (f : M →* N) (M' : Submonoid M) :
    Function.Surjective (f.submonoidMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end

section

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submonoid N) = ⊤ := (Submonoid.top_prod _).trans <| Submonoid.comap_top _

end
