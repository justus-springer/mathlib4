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

variable [PreirreducibleSpace X] [Nonempty Y]

@[simps]
noncomputable def comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    X.PartialMap Z where
  domain := f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain
  dense_domain := by
    obtain ⟨_, hx, ⟨x, rfl⟩⟩ :=
      f.hom.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
    exact (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).2.dense ⟨x.1, ⟨x, hx, rfl⟩⟩
  hom := (f.domain.ι.isoImage _).inv ≫ (f.hom ∣_ g.domain) ≫ g.hom

lemma comp_restrict_left (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) (g : Y.PartialMap Z) :
    (f.restrict U hU hU').comp g = (f.comp g).restrict (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain ⊓ U)
      ((f.comp g).dense_domain.inter_of_isOpen_right hU U.2) inf_le_left := by
  sorry

lemma comp_restrict_right (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (V : Y.Opens) (hV : Dense (V : Set Y)) (hV' : V ≤ g.domain) :
    f.comp (g.restrict V hV hV') = (f.comp g).restrict
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) (by 
        apply (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ V).2.dense
        simp
        sorry
        ) sorry := by
  sorry

lemma comp_equiv_of_equiv_left (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
    (h : f₁.equiv f₂) (g : Y.PartialMap Z) :
    (f₁.comp g).equiv (f₂.comp g) := sorry

lemma comp_equiv_of_equiv_right (f : X.PartialMap Y) [IsDominant f.hom] (g₁ g₂ : Y.PartialMap Z)
    (h : g₁.equiv g₂) : (f.comp g₁).equiv (f.comp g₂) := sorry

lemma comp_equiv_of_equiv (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
    (hf : f₁.equiv f₂) (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) :
    (f₁.comp g₁).equiv (f₂.comp g₂) :=
  equivalence_rel.trans (comp_equiv_of_equiv_left _ _ hf _) (comp_equiv_of_equiv_right _ _ _ hg)

lemma comp_toPartialMap (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z) :
    f.comp g.toPartialMap = f.compHom g := by
  ext x
  · constructor
    · intro ⟨⟨_, h₁⟩, _, h₂⟩
      exact h₂ ▸ h₁
    · intro hx
      sorry
  · simp
    sorry

variable (X) in
protected abbrev id : X.PartialMap X := (𝟙 X : X ⟶ X).toPartialMap

lemma comp_id [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] : f.comp (PartialMap.id Y) = f := by
  simp [PartialMap.comp_toPartialMap]

lemma id_comp [IrreducibleSpace X] (f : X.PartialMap Y) :
    (PartialMap.id X).comp f = f := by
  ext x
  · sorry
  · simp
    sorry

end PartialMap

noncomputable def RationalMap.comp [PreirreducibleSpace X] [Nonempty Y]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) : X ⤏ Z :=
  Quotient.liftOn g (PartialMap.toRationalMap ∘ f.dominantRep.comp) <| fun _ _ h ↦ by
    rw [Function.comp_apply, Function.comp_apply, PartialMap.toRationalMap_eq_iff]
    exact PartialMap.comp_equiv_of_equiv_right _ _ _ h

instance [PreirreducibleSpace X] [Nonempty Y] (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
    [g.IsDominant] : (f.comp g).IsDominant := sorry

lemma RationalMap.comp_toRationalMap [PreirreducibleSpace X] [Nonempty Y] (f : X ⤏ Y)
    [f.IsDominant] (g : Y.PartialMap Z) :
    f.comp g.toRationalMap = (f.dominantRep.comp g).toRationalMap :=
  rfl

variable (X) in
abbrev RationalMap.id : X ⤏ X := (𝟙 X : X ⟶ X).toRationalMap

end Scheme

end AlgebraicGeometry
