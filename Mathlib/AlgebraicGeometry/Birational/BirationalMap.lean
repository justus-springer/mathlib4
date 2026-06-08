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

@[stacks 0BAA "(1)"]
lemma BirationalMap.birational (f : X.BirationalMap Y) : X.Birational Y := by
  let e := f.hom_comp_inv_id
  rw [← f.inv.toRationalMap_representative, RationalMap.comp_def, RationalMap.id,
    PartialMap.toRationalMap_eq_iff, PartialMap.equiv_id_iff] at e
  obtain ⟨U, hU₁, hU₂, h⟩ := e
  simp at h
  -- TODO
  sorry


end Scheme

end AlgebraicGeometry
