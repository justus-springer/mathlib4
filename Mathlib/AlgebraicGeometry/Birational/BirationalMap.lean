/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition
/-!

# Birational maps between schemes

## TODO

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

structure BirationalMap (X Y : Scheme.{u}) [IrreducibleSpace X] [IrreducibleSpace Y] where
  hom : X ⤏ Y
  [isDominant_hom : hom.IsDominant]
  inv : Y ⤏ X
  [isDominant_inv : inv.IsDominant]
  hom_comp_inv_id : hom.comp inv = .id X := by grind
  inv_comp_hom_id : inv.comp hom = .id Y := by grind

attribute [instance] BirationalMap.isDominant_hom BirationalMap.isDominant_inv

attribute [simp, grind =] BirationalMap.hom_comp_inv_id BirationalMap.inv_comp_hom_id

namespace BirationalMap

variable {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

@[ext, grind ext]
lemma ext (f g : X.BirationalMap Y) (e : f.hom = g.hom) : f = g := by
  suffices f.inv = g.inv by grind [BirationalMap]
  calc
    f.inv = f.inv.comp (g.hom.comp g.inv) := by grind
    _     = g.inv := by grind

variable (X) in
@[simps, refl]
def refl : X.BirationalMap X where
  hom := RationalMap.id X
  inv := RationalMap.id X

@[simps, symm]
def symm (f : X.BirationalMap Y) : Y.BirationalMap X where
  hom := f.inv
  inv := f.hom

@[simps, trans]
noncomputable def trans (f : X.BirationalMap Y) (g : Y.BirationalMap Z) :
    BirationalMap X Z where
  hom := f.hom.comp g.hom
  inv := g.inv.comp f.inv

@[simp]
theorem refl_trans (f : X.BirationalMap Y) : (BirationalMap.refl X).trans f = f := by
  ext; simp

@[simp]
theorem trans_refl (f : X.BirationalMap Y) : f.trans (BirationalMap.refl Y) = f := by
  ext; simp

@[simp, grind _=_]
theorem trans_symm (f : X.BirationalMap Y) (g : Y.BirationalMap Z) :
    (f.trans g).symm = g.symm.trans f.symm := by
  ext; simp

@[simp]
theorem symm_trans_self_id (f : X.BirationalMap Y) : f.symm.trans f = BirationalMap.refl Y := by
  ext; simp

@[simp]
theorem self_trans_symm_id (f : X.BirationalMap Y) : f.trans f.symm = BirationalMap.refl X := by
  ext; simp

@[simp, grind _=_]
theorem trans_assoc {W : Scheme.{u}} [IrreducibleSpace W]
    (f : X.BirationalMap Y) (g : Y.BirationalMap Z) (h : Z.BirationalMap W) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext; simp only [BirationalMap.trans_hom, f.hom.comp_assoc]

noncomputable instance : Group (X.BirationalMap X) where
  one := refl X
  inv := symm
  mul := trans
  mul_assoc := trans_assoc
  one_mul := refl_trans
  mul_one := trans_refl
  inv_mul_cancel := symm_trans_self_id

end BirationalMap

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

lemma PartialIso.toPartialMap_comp_symm (f : X.PartialIso Y) :
    f.toPartialMap.comp f.symm.toPartialMap =
      (PartialMap.id X).restrict f.source f.dense_source le_top := by
  ext1
  · -- This change seems hard to remove
    change f.source.ι ''ᵁ f.iso.hom ⁻¹ᵁ f.target.ι ⁻¹ᵁ f.target = f.source
    rw [Opens.ι_preimage_self, Hom.preimage_top, Opens.ι_image_top]
  · -- This change seems hard to remove
    change (f.source.ι.isoImage (f.iso.hom ⁻¹ᵁ f.target.ι ⁻¹ᵁ f.target)).inv ≫
      (f.iso.hom ≫ f.target.ι) ∣_ f.target ≫ f.iso.inv ≫ f.source.ι = _
    simp_rw [morphismRestrict_comp, Opens.morphismRestrict_ι, homOfLE_ι,
      morphismRestrict_ι, Category.assoc, Iso.hom_inv_id_assoc, Hom.isoImage_inv_ι, isoOfEq_hom,
      PartialMap.restrict_hom, PartialMap.id_domain, Hom.toPartialMap_hom, topIso_hom,
      Category.comp_id, homOfLE_ι]
    exact (X.homOfLE_ι _).symm

lemma PartialIso.symm_toPartialMap_comp (f : X.PartialIso Y) :
    f.symm.toPartialMap.comp f.toPartialMap =
      (PartialMap.id Y).restrict f.target f.dense_target le_top := by
  ext1
  · -- This change seems hard to remove
    change f.target.ι ''ᵁ f.iso.inv ⁻¹ᵁ f.source.ι ⁻¹ᵁ f.source = f.target
    rw [Opens.ι_preimage_self, Hom.preimage_top, Opens.ι_image_top]
  · -- This change seems hard to remove
    change (f.target.ι.isoImage (f.iso.inv ⁻¹ᵁ f.source.ι ⁻¹ᵁ f.source)).inv ≫
      (f.iso.inv ≫ f.source.ι) ∣_ f.source ≫ f.iso.hom ≫ f.target.ι = _
    simp_rw [morphismRestrict_comp, Opens.morphismRestrict_ι, homOfLE_ι,
      morphismRestrict_ι, Category.assoc, Iso.inv_hom_id_assoc, Hom.isoImage_inv_ι, isoOfEq_hom,
      PartialMap.restrict_hom, PartialMap.id_domain, Hom.toPartialMap_hom, topIso_hom,
      Category.comp_id, homOfLE_ι]
    exact (Y.homOfLE_ι _).symm

def PartialIso.toBirationalMap (f : X.PartialIso Y) : X.BirationalMap Y where
  hom := f.toRationalMap
  inv := f.symm.toRationalMap
  hom_comp_inv_id := by
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff,
      PartialIso.toPartialMap_comp_symm]
    apply PartialMap.restrict_equiv
  inv_comp_hom_id := by
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff,
      PartialIso.symm_toPartialMap_comp]
    apply PartialMap.restrict_equiv

/-
If `g` is an open immersion, is `f ≫ g` always an open immersion?
-/
@[stacks 0BAA "(1)"]
lemma BirationalMap.birational (b : X.BirationalMap Y) : X.Birational Y := by
  let f := b.hom.representative
  let g := b.inv.representative
  let U₀ := f.domain
  let V₀ := g.domain
  have f_comp_g : (f.comp g).equiv (PartialMap.id X) := by
    have := b.hom_comp_inv_id
    rw [← b.inv.toRationalMap_representative, RationalMap.comp_def, RationalMap.id,
      PartialMap.toRationalMap_eq_iff] at this
    exact this
  rw [PartialMap.equiv_id_iff] at f_comp_g
  obtain ⟨U₁, dense_U₁, U₁_le : U₁ ≤ U₀.ι ''ᵁ f.hom ⁻¹ᵁ V₀, hU₁⟩ := f_comp_g
  have U₁_le_U₀ : U₁ ≤ U₀ := U₁_le.trans (U₀.ι_image_le _)
  change X.homOfLE U₁_le ≫ (U₀.ι.isoImage (f.hom ⁻¹ᵁ V₀)).inv ≫ f.hom ∣_ V₀ ≫ g.hom = U₁.ι at hU₁
  let U₂ : Opens U₀ := U₀.ι ⁻¹ᵁ U₁
  have U₂_le : U₂ ≤ f.hom ⁻¹ᵁ V₀ := by
    have := Hom.preimage_mono U₀.ι U₁_le
    simp only [Hom.preimage_image_eq] at this
    exact this
  have U₁_eq : U₁ = U₀.ι ''ᵁ U₂ := by
    have := (opensRestrict U₀).apply_symm_apply ⟨U₁, U₁_le_U₀⟩
    exact congr($this.1).symm
  let f' := f.restrict U₁ dense_U₁ U₁_le_U₀
  let g' := g.restrict (V₀.ι ''ᵁ g.hom ⁻¹ᵁ U₁) ((g.comp f').dense_domain) (V₀.ι_image_le _)
  have g'_comp_f' : (g'.comp f').equiv (PartialMap.id Y) := by
    have foo₁ := f.restrict_equiv U₁ dense_U₁ U₁_le_U₀
    have foo₂ := g.restrict_equiv (V₀.ι ''ᵁ g.hom ⁻¹ᵁ U₁) ((g.comp f').dense_domain) (V₀.ι_image_le _)
    have foo₃ : (g'.comp f').equiv (g.comp f) := PartialMap.comp_equiv_of_equiv _ _ foo₂ _ _ foo₁
    have := b.inv_comp_hom_id
    rw [← b.hom.toRationalMap_representative, RationalMap.comp_def, RationalMap.id,
      PartialMap.toRationalMap_eq_iff] at this
    exact foo₃.trans this
  rw [PartialMap.equiv_id_iff] at g'_comp_f'
  obtain ⟨V₁, dense_V₁, V₁_le, hV₁⟩ := g'_comp_f'

  -- change hV₁
  unfold g' at hV₁
  simp only [PartialMap.restrict_hom, PartialMap.comp_hom] at hV₁
  conv at hV₁ =>
    lhs;
    enter [2]
    change (Hom.isoImage (V₀.ι ''ᵁ g.hom ⁻¹ᵁ U₁).ι
      (Y.homOfLE (V₀.ι_image_le (g.hom ⁻¹ᵁ U₁)) ⁻¹ᵁ g.hom ⁻¹ᵁ U₁)).inv ≫ _
    enter [2]
    change (_ ≫ _) ∣_ _ ≫ _
    rw [morphismRestrict_comp]
    change ((Y.homOfLE _) ∣_ (g.hom ⁻¹ᵁ U₁) ≫ g.hom ∣_ U₁) ≫ _
    rw [Category.assoc]
    enter [2, 2]
    change X.homOfLE U₁_le_U₀ ≫ f.hom
  erw [isoImage_ι_inv_morphismRestrict_homOfLE_assoc (V₀.ι_image_le (g.hom ⁻¹ᵁ U₁)) (g.hom ⁻¹ᵁ U₁)] at hV₁
  erw [homOfLE_homOfLE_assoc] at hV₁
  

  have V₁_le_V₀_ι : V₁ ≤ V₀.ι ''ᵁ g.hom ⁻¹ᵁ U₁ := by
    exact V₁_le.trans (Opens.ι_image_le _ _)
  have V₁_le_V₀ : V₁ ≤ V₀ := V₁_le_V₀_ι.trans (V₀.ι_image_le _)
  let V₂ : Opens V₀ := V₀.ι ⁻¹ᵁ V₁
  have V₂_le : V₂ ≤ g.hom ⁻¹ᵁ U₁ := by
    have := Hom.preimage_mono V₀.ι V₁_le_V₀_ι
    simp only [Hom.preimage_image_eq] at this
    exact this
  have V₁_eq : V₁ = V₀.ι ''ᵁ V₂ := by
    have := (opensRestrict V₀).apply_symm_apply ⟨V₁, V₁_le_V₀⟩
    exact congr($this.1).symm
  have U₂_le_new : U₂ ≤ f.hom ⁻¹ᵁ V₁ := by
    intro x hx
    simp
    sorry
  
  -- continue changing hV₁
  rw [← Y.homOfLE_homOfLE V₁_eq.le (V₀.ι.image_mono V₂_le)] at hV₁
  rw [Category.assoc] at hV₁
  rw [← V₀.ι.isoImage_inv_homOfLE_assoc _ _ V₂_le] at hV₁

  -- define the isos
  let i := Y.homOfLE V₁_eq.le ≫ (V₀.ι.isoImage V₂).inv ≫ g.hom.resLE U₁ V₂ V₂_le
  let j := X.homOfLE U₁_eq.le ≫ (U₀.ι.isoImage U₂).inv ≫ f.hom.resLE V₁ U₂ U₂_le_new
  refine ⟨U₁, dense_U₁, V₁, dense_V₁, ⟨j, i, ?_, ?_⟩⟩
  · -- hard?
    sorry
  · unfold i j Hom.resLE
    rw [← cancel_mono V₁.ι]
    simp only [Category.assoc, Category.id_comp]
    simp only [morphismRestrict_ι, homOfLE_ι_assoc, Opens.isoImage_ι_inv_ι_assoc,
      homOfLE_homOfLE_assoc]
    exact hV₁

end Scheme

end AlgebraicGeometry
