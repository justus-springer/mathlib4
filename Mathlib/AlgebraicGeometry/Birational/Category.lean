/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
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

lemma PartialMap.restrict_comp [PreirreducibleSpace X] [Nonempty Y] (f : X.PartialMap Y)
    [IsDominant f.hom] (U : X.Opens) (hU : Dense (U : Set X))
    (hU' : U ≤ f.domain) (g : Y.PartialMap Z) :
    (f.restrict U hU hU').comp g = (f.comp g).restrict
      (opensRestrict _ (f.hom ⁻¹ᵁ g.domain) ⊓ U)
      ((f.comp g).dense_domain.inter_of_isOpen_right hU U.2) inf_le_left := by
  ext x
  · constructor
    · intro ⟨x', h₁, h₂⟩
      refine ⟨?_, ?_⟩
      simp at *
      sorry
    · sorry
  · sorry

lemma PartialMap.comp_restrict [PreirreducibleSpace X] [Nonempty Y] (f : X.PartialMap Y)
    [IsDominant f.hom] (g : Y.PartialMap Z) (V : Y.Opens) (hV : Dense (V : Set Y))
    (hV' : V ≤ g.domain) :
    f.comp (g.restrict V hV hV') = (f.comp g).restrict
      (opensRestrict _ (f.hom ⁻¹ᵁ V)) sorry sorry := by
  sorry

lemma PartialMap.comp_equiv_of_equiv_left [PreirreducibleSpace X] [Nonempty Y]
    (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
    (h : f₁.equiv f₂) (g : Y.PartialMap Z) :
    (f₁.comp g).equiv (f₂.comp g) := sorry

lemma PartialMap.comp_equiv_of_equiv_right [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g₁ g₂ : Y.PartialMap Z) (h : g₁.equiv g₂) :
    (f.comp g₁).equiv (f.comp g₂) := sorry

lemma PartialMap.comp_equiv_of_equiv [PreirreducibleSpace X] [Nonempty Y]
    (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom] (hf : f₁.equiv f₂)
    (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) :
    (f₁.comp g₁).equiv (f₂.comp g₂) := sorry

noncomputable def RationalMap.comp [PreirreducibleSpace X] [Nonempty Y]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) : X ⤏ Z :=
  Quotient.liftOn g (PartialMap.toRationalMap ∘ f.dominantRep.comp) <| fun _ _ h ↦ by
    rw [Function.comp_apply, Function.comp_apply, PartialMap.toRationalMap_eq_iff]
    exact PartialMap.comp_equiv_of_equiv_right _ _ _ h

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

