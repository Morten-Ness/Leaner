import Mathlib

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem centralizer_centralizer_centralizer {s : Set A} :
    Subalgebra.centralizer R s.centralizer.centralizer = Subalgebra.centralizer R s := by
  apply SetLike.coe_injective
  simp only [Subalgebra.coe_centralizer, Set.centralizer_centralizer_centralizer]

end

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem centralizer_univ : Subalgebra.centralizer R Set.univ = Subalgebra.center R A := SetLike.ext' (Set.centralizer_univ A)

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 := OneMemClass.coe_eq_one

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype

end

section

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem comap_map_eq_self_of_injective
    {f : A →ₐ[R] B} (hf : Function.Injective f) (S : Subalgebra R A) : (S.map f).comap f = S := SetLike.coe_injective (Set.preimage_image_eq _ hf)

end

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem inclusion_injective : Function.Injective (Subalgebra.inclusion h) := fun _ _ => Subtype.ext ∘ Subtype.mk.inj

end

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem inclusion_self : Subalgebra.inclusion (le_refl S) = AlgHom.id R S := AlgHom.ext fun _x => Subtype.ext rfl

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (φ : A →ₐ[R] B)

theorem injective_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    Function.Injective (f.codRestrict S hf) ↔ Function.Injective f := ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S := SetLike.coe_injective <| Set.image_id _

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem map_injective {f : A →ₐ[R] B} (hf : Function.Injective f) : Function.Injective (Subalgebra.map f) := fun _S₁ _S₂ ih =>
  Subalgebra.ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem map_map (S : Subalgebra R A) (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) := SetLike.coe_injective <| Set.image_image _ _ _

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (φ : A →ₐ[R] B)

theorem rangeRestrict_surjective (f : A →ₐ[R] B) : Function.Surjective (f.rangeRestrict) := fun ⟨_y, hy⟩ =>
    let ⟨x, hx⟩ := hy
    ⟨x, SetCoe.ext hx⟩

end

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable {α β : Type*}

theorem rangeS_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).rangeS = S.toSubsemiring := by
  rw [Subalgebra.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp, ← Subalgebra.toSubsemiring_subtype,
    Subsemiring.rangeS_subtype]

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r

end

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable {α β : Type*}

theorem range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).range = S.toSubring := by
  rw [Subalgebra.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp, ← Subalgebra.toSubring_subtype,
    Subring.range_subtype]

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (φ : A →ₐ[R] B)

theorem range_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range = f.range.map g := SetLike.coe_injective (Set.range_comp g f)

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (φ : A →ₐ[R] B)

theorem range_comp_le_range (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range ≤ g.range := SetLike.coe_mono (Set.range_comp_subset_range f g)

end

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable (f : A →ₐ[R] B)

theorem range_comp_val : (f.comp S.val).range = S.map f := by
  rw [AlgHom.range_comp, Subalgebra.range_val]

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

end

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

theorem range_val : S.val.range = S := Subalgebra.ext <| Set.ext_iff.1 <| S.val.coe_range.trans Subtype.range_val

end

section

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable {α β : Type*}

theorem setRange_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : Set.range (algebraMap S A) = (S : Set A) := SetLike.ext'_iff.mp S.rangeS_algebraMap

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toNonUnitalSubalgebra_inj {S U : Subalgebra R A} :
    S.toNonUnitalSubalgebra = U.toNonUnitalSubalgebra ↔ S = U := Subalgebra.toNonUnitalSubalgebra_injective.eq_iff

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toNonUnitalSubalgebra_injective : Function.Injective
    (Subalgebra.toNonUnitalSubalgebra : Subalgebra R A → NonUnitalSubalgebra R A) := fun _ _ ↦ by simp [SetLike.ext_iff]

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toSubmodule_injective : Function.Injective (Subalgebra.toSubmodule : Subalgebra R A → Submodule R A) := fun _S₁ _S₂ h => SetLike.ext (SetLike.ext_iff.mp h :)

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toSubring_inj {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S U : Subalgebra R A} : S.toSubring = U.toSubring ↔ S = U := Subalgebra.toSubring_injective.eq_iff

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] :
    Function.Injective (Subalgebra.toSubring : Subalgebra R A → Subring A) := fun S T h =>
  Subalgebra.ext fun x => by rw [← Subalgebra.mem_toSubring, ← Subalgebra.mem_toSubring, h]

end

section

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem toSubsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiring ↔ S = U := Subalgebra.toSubsemiring_injective.eq_iff

end
