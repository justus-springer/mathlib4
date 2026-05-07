/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# The category of schemes with birational maps

## TODO

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)

namespace Scheme

variable (X) in
abbrev PartialMap.id : X.PartialMap X := (𝟙 X : X ⟶ X).toPartialMap

@[simps]
noncomputable def PartialMap.comp [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) : X.PartialMap Z where
  domain := opensRestrict _ (f.hom ⁻¹ᵁ g.domain)
  dense_domain := by
    obtain ⟨_, hx, ⟨x, rfl⟩⟩ :=
      f.hom.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
    exact (opensRestrict _ (f.hom ⁻¹ᵁ g.domain)).1.2.dense ⟨x.1, ⟨x, hx, rfl⟩⟩
  hom := (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ (f.hom ∣_ g.domain) ≫ g.hom

lemma PartialMap.comp_toPartialMap [PreirreducibleSpace X] [Nonempty Y] (f : X.PartialMap Y)
    [IsDominant f.hom] (g : Y ⟶ Z) : f.comp g.toPartialMap = f.compHom g := by
  ext x
  · constructor
    · intro ⟨⟨_, h₁⟩, _, h₂⟩
      exact h₂ ▸ h₁
    · intro hx
      simp only [PartialMap.comp_domain, Hom.toPartialMap_domain, TopologicalSpace.Opens.map_top,
        coe_opensRestrict_apply_coe, TopologicalSpace.Opens.coe_top, Set.image_univ, Set.mem_range]
      exact ⟨⟨x, hx⟩, rfl⟩
  · simp
    sorry

lemma PartialMap.comp_id [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] : f.comp (PartialMap.id Y) = f := by
  simp [PartialMap.comp_toPartialMap]

lemma PartialMap.id_comp [IrreducibleSpace X] (f : X.PartialMap Y) :
    (PartialMap.id X).comp f = f := by
  ext x
  · sorry
  · simp
    sorry

noncomputable def RationalMap.comp [IrreducibleSpace X] [IrreducibleSpace Y]
  (f : X ⤏ Y) (g : Y ⤏ Z) : X ⤏ Z := sorry
