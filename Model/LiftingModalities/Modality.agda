--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------

open import Model.BaseCategory
open import Model.Modality

module Model.LiftingModalities.Modality {C V W : BaseCategory} (μ : Modality V W) where

open import Model.LiftingModalities.Context {C} μ
open import Model.LiftingModalities.Type {C} μ
open import Model.LiftingModalities.Term {C} μ

private
  C×V : BaseCategory
  C×V = C ⊗ V

  C×W : BaseCategory
  C×W = C ⊗ W 


--------------------------------------------------
-- Modality

lifted : Modality C×V C×W
ctx-functor lifted = lift-ctx-functor
⟨ lifted ∣ T ⟩ = lift-ty T
mod-hom lifted = lift-mod-hom
mod-hom-refl lifted = lift-mod-hom-refl
mod-hom-trans lifted = lift-mod-hom-trans
mod-hom-cong lifted = lift-mod-hom-cong
mod-natural lifted = lift-mod-natural
mod-natural-hom lifted = lift-mod-natural-hom
mod-natural-idⁿ lifted = lift-mod-natural-idⁿ
mod-natural-⊚ⁿ lifted = lift-mod-natural-⊚ⁿ
mod-natural-subst-eqⁿ lifted = lift-mod-natural-subst-eqⁿ
mod-intro lifted = lift-tm
mod-intro-cong lifted = lift-mod-intro-cong
mod-intro-natural lifted = lift-mod-intro-natural
mod-intro-convert lifted = lift-mod-intro-convert
mod-elim lifted = lift-tm⁻¹
mod-elim-cong lifted = lift-tm⁻¹-cong
mod-β lifted = lift-mod-β
mod-η lifted = lift-mod-η
