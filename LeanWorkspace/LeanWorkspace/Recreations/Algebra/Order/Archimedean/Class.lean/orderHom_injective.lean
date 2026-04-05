import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

theorem orderHom_injective {f : M →*o N} (h : Function.Injective f) :
    Function.Injective (MulArchimedeanClass.orderHom f) := by
  intro a b
  induction a using MulArchimedeanClass.ind with | MulArchimedeanClass.mk a
  induction b using MulArchimedeanClass.ind with | MulArchimedeanClass.mk b
  simp_rw [MulArchimedeanClass.orderHom_mk, MulArchimedeanClass.mk_eq_mk, ← map_mabs, ← map_pow]
  obtain hmono := (OrderHomClass.monotone f).strictMono_of_injective h
  intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  exact ⟨⟨m, hmono.le_iff_le.mp hm⟩, ⟨n, hmono.le_iff_le.mp hn⟩⟩

