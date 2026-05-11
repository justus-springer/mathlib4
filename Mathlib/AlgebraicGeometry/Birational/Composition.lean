/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
/-!

# Composition of rational maps

## TODO

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

namespace Scheme

namespace PartialMap

section

variable [PreirreducibleSpace X] [Nonempty Y]

theorem _root_.Set.nonempty_preimage_iff {α β} {s : Set β} {f : α → β} :
    (f ⁻¹' s).Nonempty ↔ (s ∩ Set.range f).Nonempty := by
  rw [Set.inter_comm]
  simpa using (Set.image_inter_nonempty_iff (s := Set.univ)).symm

@[simps]
noncomputable def comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    X.PartialMap Z where
  domain := f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain
  dense_domain := (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).2.dense <| by
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
  hom := (f.domain.ι.isoImage _).inv ≫ (f.hom ∣_ g.domain) ≫ g.hom

attribute [local instance] PartialMap.isDominant_restrict_hom in
lemma comp_restrict_left (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) (g : Y.PartialMap Z) :
    (f.restrict U hU hU').comp g = (f.comp g).restrict (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain ⊓ U)
      ((f.comp g).dense_domain.inter_of_isOpen_right hU U.2) inf_le_left := by
  ext1
  · simp only [comp_domain, restrict_domain, restrict_hom, Hom.comp_preimage,
      ι_image_homOfLE_eq_ι_image_inf]
  · simp only [comp_hom, comp_domain, restrict_hom, restrict_domain, Hom.comp_preimage,
      morphismRestrict_comp, Category.assoc, isoOfEq_hom, homOfLE_homOfLE_assoc,
      ι_isoImage_inv_morphismRestrict_homOfLE_assoc]

lemma comp_restrict_right (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (V : Y.Opens) (hV : Dense (V : Set Y)) (hV' : V ≤ g.domain) :
    f.comp (g.restrict V hV hV') = (f.comp g).restrict
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) ((f.domain.ι ''ᵁ f.hom ⁻¹ᵁ V).2.dense <| by
          simpa [← Set.nonempty_preimage_iff] using
            f.hom.denseRange.inter_open_nonempty _ V.2 hV.nonempty)
      (f.domain.ι.image_mono (f.hom.preimage_mono hV')) := by
  ext1
  · rfl
  · simp only [comp_domain, restrict_domain, comp_hom, restrict_hom, isoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, ← f.domain.ι.isoImage_inv_homOfLE_assoc _ _ (f.hom.preimage_mono hV'),
      ← morphismRestrict_homOfLE_assoc f.hom _ _ hV']

attribute [local instance] PartialMap.isDominant_restrict_hom in
lemma comp_equiv_of_equiv_left (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
    (h : f₁.equiv f₂) (g : Y.PartialMap Z) :
    (f₁.comp g).equiv (f₂.comp g) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : f₁.restrict W hW hW₁ = f₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr($(e).comp g)
  rw [comp_restrict_left, comp_restrict_left] at e
  exact equiv_of_restrict_eq _ _ e

lemma comp_equiv_of_equiv_right (f : X.PartialMap Y) [IsDominant f.hom] (g₁ g₂ : Y.PartialMap Z)
    (h : g₁.equiv g₂) : (f.comp g₁).equiv (f.comp g₂) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : g₁.restrict W hW hW₁ = g₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr(f.comp $e)
  rw [comp_restrict_right, comp_restrict_right] at e
  exact equiv_of_restrict_eq _ _ e

lemma comp_equiv_of_equiv (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
    (hf : f₁.equiv f₂) (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) :
    (f₁.comp g₁).equiv (f₂.comp g₂) :=
  equivalence_rel.trans (comp_equiv_of_equiv_left _ _ hf _) (comp_equiv_of_equiv_right _ _ _ hg)


end

@[simp]
lemma comp_toPartialMap [PreirreducibleSpace X] [Nonempty Y] (f : X.PartialMap Y)
    [IsDominant f.hom] (g : Y ⟶ Z) : f.comp g.toPartialMap = f.compHom g := by
  ext1
  · simp
  · dsimp only [comp_domain, Hom.toPartialMap_domain, TopologicalSpace.Opens.map_top, comp_hom,
    Hom.toPartialMap_hom, topIso_hom, compHom_domain, compHom_hom]
    erw [morphismRestrict_ι_assoc f.hom ⊤ g]
    sorry
    -- todo

lemma comp_id [PreirreducibleSpace X] [Nonempty Y] (f : X.PartialMap Y) [IsDominant f.hom] :
    f.comp (PartialMap.id Y) = f := by simp

@[simp]
lemma id_comp [IrreducibleSpace X] (f : X.PartialMap Y) : (PartialMap.id X).comp f = f := by
  ext1
  · simp
    sorry
  · simp
    sorry

end PartialMap

noncomputable def RationalMap.comp [PreirreducibleSpace X] [Nonempty Y]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) : X ⤏ Z :=
  Quotient.liftOn g (PartialMap.toRationalMap ∘ f.dominantRep.comp) <| fun _ _ h ↦ by
    rw [Function.comp_apply, Function.comp_apply, PartialMap.toRationalMap_eq_iff]
    exact PartialMap.comp_equiv_of_equiv_right _ _ _ h

@[simp]
lemma RationalMap.comp_toRationalMap [PreirreducibleSpace X] [Nonempty Y] (f : X ⤏ Y)
    [f.IsDominant] (g : Y.PartialMap Z) :
    f.comp g.toRationalMap = (f.dominantRep.comp g).toRationalMap :=
  rfl

lemma PartialMap.toRationalMap_comp [PreirreducibleSpace X] [Nonempty Y] (f : X.PartialMap Y)
    [IsDominant f.hom] (g : Y ⤏ Z) (g' : Y.PartialMap Z) (h : g'.toRationalMap = g) :
    f.toRationalMap.comp g = (f.comp g').toRationalMap := sorry

lemma RationalMap.comp_id [PreirreducibleSpace X] [Nonempty Y] (f : X ⤏ Y) [f.IsDominant] :
    f.comp (RationalMap.id Y) = f := by simp

@[simp]
lemma RationalMap.id_comp [IrreducibleSpace X] (f : X ⤏ Y) [f.IsDominant] :
    (RationalMap.id X).comp f = f := by
  simp [(PartialMap.id X).toRationalMap_comp _ _ f.toRationalMap_dominantRep]

instance [PreirreducibleSpace X] [Nonempty Y] (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
    [g.IsDominant] : (f.comp g).IsDominant := sorry

end Scheme

end AlgebraicGeometry
