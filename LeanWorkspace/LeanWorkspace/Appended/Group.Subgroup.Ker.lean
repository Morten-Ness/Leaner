import Mathlib

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem apply_ofInjective_symm {f : G →* N} (hf : Function.Injective f) (x : f.range) :
    f ((MonoidHom.ofInjective hf).symm x) = x := Subtype.ext_iff.1 <| (MonoidHom.ofInjective hf).apply_symm_apply x

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_le_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f ≤ L.comap f ↔ K ≤ L := Subgroup.comap_le_comap_of_le_range (MonoidHom.range_eq_top.2 hf ▸ le_top)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_lt_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f < L.comap f ↔ K < L := by simp_rw [lt_iff_le_not_ge, Subgroup.comap_le_comap_of_surjective hf]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem div_mem_ker_iff (f : G →* M) {x y : G} : x / y ∈ MonoidHom.ker f ↔ f x = f y := by
  constructor <;> intro h
  · rw [← div_mul_cancel x y, map_mul, MonoidHom.mem_ker.mp h, one_mul]
  · rw [MonoidHom.mem_ker, div_eq_mul_inv, map_mul, h, ← map_mul, mul_inv_cancel, map_one]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [Monoid M]

theorem eqLocus_same (f : G →* N) : f.eqLocus f = ⊤ := SetLike.ext fun _ => eq_self_iff_true _

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem eq_iff (f : G →* M) {x y : G} : f x = f y ↔ y⁻¹ * x ∈ f.ker := by
  constructor <;> intro h
  · rw [MonoidHom.mem_ker, map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  · rw [← one_mul x, ← mul_inv_cancel y, mul_assoc, map_mul, MonoidHom.mem_ker.1 h, mul_one]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : G →* N) (s : S)
    (h : ∀ x, f x ∈ s) : (f.codRestrict s h).ker = f.ker := SetLike.ext fun _x => Subtype.ext_iff

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_one : (1 : G →* M).ker = ⊤ := SetLike.ext fun _x => eq_self_iff_true _

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_prod {M N : Type*} [MulOneClass M] [MulOneClass N] (f : G →* M) (g : G →* N) :
    (f.prod g).ker = f.ker ⊓ g.ker := SetLike.ext fun _ => Prod.mk_eq_one

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_toHomUnits {M} [Monoid M] (f : G →* M) : f.toHomUnits.ker = f.ker := by
  ext x
  simp [MonoidHom.mem_ker, Units.ext_iff]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_eq_map_iff {f : G →* N} {H K : Subgroup G} :
    H.map f = K.map f ↔ H ⊔ f.ker = K ⊔ f.ker := by simp only [le_antisymm_iff, Subgroup.map_le_map_iff']

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_eq_range_iff {f : G →* N} {H : Subgroup G} :
    H.map f = f.range ↔ Codisjoint H f.ker := by
  rw [MonoidHom.range_eq_map f, Subgroup.map_eq_map_iff, codisjoint_iff, top_sup_eq]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_le_map_iff' {f : G →* N} {H K : Subgroup G} :
    H.map f ≤ K.map f ↔ H ⊔ f.ker ≤ K ⊔ f.ker := by
  simp only [Subgroup.map_le_map_iff, sup_le_iff, le_sup_right, and_true]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_lt_map_iff_of_injective {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f < K.map f ↔ H < K := lt_iff_lt_of_le_iff_le' (Subgroup.map_le_map_iff_of_injective hf) (Subgroup.map_le_map_iff_of_injective hf)

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem map_range (g : N →* P) (f : G →* N) : f.range.map g = (g.comp f).range := by
  rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map]; exact (⊤ : Subgroup G).map_map g f

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {M N : Type*} [CommGroup M] [CommGroup N]

theorem map_range_powMonoidHom (e : M ≃* N) (n : ℕ) :
    (powMonoidHom (α := M) n).range.map e = (powMonoidHom (α := N) n).range := by
  have H : (e : M →* N).comp (powMonoidHom n) = (powMonoidHom n).comp e := by ext : 1; simp
  rw [MonoidHom.map_range, H, MonoidHom.range_comp, MulEquiv.range_eq_top e, ← MonoidHom.range_eq_map]

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_le {H : Subgroup G} (K : Subgroup H) : K.map H.subtype ≤ H := (K.map_le_range H.subtype).trans_eq H.range_subtype

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_le_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype ≤ K.map G'.subtype ↔ H ≤ K := Subgroup.map_le_map_iff_of_injective G'.subtype_injective

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_lt_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype < K.map G'.subtype ↔ H < K := Subgroup.map_lt_map_iff_of_injective G'.subtype_injective

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem rangeRestrict_injective_iff {f : G →* N} : Function.Injective f.rangeRestrict ↔ Function.Injective f := by
  convert Set.injective_codRestrict _

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem range_one : (1 : G →* N).range = ⊥ := SetLike.ext fun x => by simpa using @comm _ (· = ·) _ 1 x

end

section

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem subgroupOf_range_eq_of_le {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K : Subgroup G₂}
    (f : G₁ →* G₂) (h : f.range ≤ K) :
    f.range.subgroupOf K = (f.codRestrict K fun x => h ⟨x, rfl⟩).range := by
  ext k
  refine exists_congr ?_
  simp [Subtype.ext_iff]

end
