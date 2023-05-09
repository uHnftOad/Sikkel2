--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Model.BaseCategory
open import Model.Modality

module Model.LiftingModalities.L-Type {C V W : BaseCategory} (μ : Modality V W) where

open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injective)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Type.Function
open import Model.LiftingModalities.L-Context {C} {V} {W} μ

open BaseCategory
open Ctx

private
  C×V : BaseCategory
  C×V = C ⊗ V

  C×W : BaseCategory
  C×W = C ⊗ W 

  variable
    Γ Δ Θ : Ctx C×W


--------------------------------------------------
-- Helper functions for defining `⟨ μ̃ ∣ _ ⟩`
module _ {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} where
  lock-fmap-naturalˡ : T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ˢ⟪ f ⟫ˡ ] [ to lift-ctx-naturalˡ ] ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]
  lock-fmap-naturalˡ = transᵗʸ (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) (lift-ctx Γ ˢ⟪ f ⟫ˡ) (to lift-ctx-naturalˡ)) 
                      (transᵗʸ (ty-subst-cong-subst lift-ctx-cong-naturalˡ (T ᵗʸ⟨ c₁ ⟩ˡ)) 
                                (symᵗʸ (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) (to lift-ctx-naturalˡ) (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)))))

  module _ (input : T ᵗʸ⟨ c₂ ⟩ˡ ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ˢ⟪ f ⟫ˡ ]) where
    s₁ : T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ˢ⟪ f ⟫ˡ ] [ to lift-ctx-naturalˡ ]
    s₁ = ty-subst-map (to lift-ctx-naturalˡ) input
    
    s₂ : T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]
    s₂ = from lock-fmap-naturalˡ ⊙ s₁

    s₃ : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ↣ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ] ⟩
    s₃ = mod-on-↣ μ s₂

    lift-ty-mor-C-helper : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ↣ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ]
    lift-ty-mor-C-helper = to (mod-natural μ (Γ ˢ⟪ f ⟫ˡ)) ⊙ s₃


--------------------------------------------------
-- ⟨ μ̃ ∣ _ ⟩

{-
  Γ @ C×W
  lift-ctx Γ ⊢ T type @ C×V
  -----------------------------------------
  lift-ctx Γ ⟨ c ⟩ˡ ⊢ T ᵗʸ⟨ c ⟩ˡ type @ V
  Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⊢ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] type @ V
  ----------------------------------------------------------------------
  Γ ⟨ c ⟩ˡ ⊢ ⟨ μ | T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ type @ W
-}
module _ {Γ : Ctx C×W} (T : Ty (lift-ctx Γ)) where
  lift-ty-obj : (cw : Ob C×W) → (γ : Γ ⟨ cw ⟩) → Set
  lift-ty-obj [ c , w ] γ = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w , γ ⟩

  -- ⟨ μ̃ ∣ T ⟩ ⟪ [ hom-id C , g ] , _ ⟫_ 
  lift-ty-mor-W : {c : Ob C} {w₁ w₂ : Ob W} → 
                  (g : Hom W w₁ w₂) →
                  {γ₂ : Γ ⟨ c ⟩ˡ ⟨ w₂ ⟩} {γ₁ : Γ ⟨ c ⟩ˡ ⟨ w₁ ⟩} → 
                  (eγ : Γ ⟨ c ⟩ˡ ⟪ g ⟫ γ₂ ≡ γ₁) → 
                  lift-ty-obj [ c , w₂ ] γ₂ → lift-ty-obj [ c , w₁ ] γ₁
  lift-ty-mor-W g eγ = ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ g , eγ ⟫_

  -- ⟨ μ̃ ∣ T ⟩ ⟪ [ f , hom-id W ] , _ ⟫_
  lift-ty-mor-C : {c₁ c₂ : Ob C} {w : Ob W} → 
                  (f : Hom C c₁ c₂) →
                  {γ₂ : Γ ⟨ w ⟩ʳ ⟨ c₂ ⟩} {γ₁ : Γ ⟨ w ⟩ʳ ⟨ c₁ ⟩} → 
                  (eγ : Γ ⟨ w ⟩ʳ ⟪ f ⟫ γ₂ ≡ γ₁) → 
                  lift-ty-obj [ c₂ , w ] γ₂ → lift-ty-obj [ c₁ , w ] γ₁
  lift-ty-mor-C {c₁} f eγ t = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) eγ ⟫ (func (lift-ty-mor-C-helper (mor-to-↣ˡ T f)) t)

  lift-ty-mor-C-refl : {c₁ c₂ : Ob C} {w : Ob W} {f : Hom C c₁ c₂} {γ : Γ ⟨ [ c₂ , w ] ⟩} {eγ : Γ ⟨ w ⟩ʳ ⟪ f ⟫ γ ≡ Γ ⟨ w ⟩ʳ ⟪ f ⟫ γ} {t : lift-ty-obj [ c₂ , w ] γ} →
                       lift-ty-mor-C f eγ t ≡ func (lift-ty-mor-C-helper (mor-to-↣ˡ T f)) t
  lift-ty-mor-C-refl {c₁} = trans (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl) (ty-id ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩) 
  
  {- 
    ⟨ μ̃ ∣ T ⟩ ⟪ [ f , g ] , _ ⟫_ 

                                                          lift-ty T ⟪ [ f , hom-id W {w₂} , refl ⟫_
    lift-ty T ⟨ [ c₁ , w₂ ] , Γ ⟪ [ f , hom-id W ] ⟫ γ₂ ⟩ ←----------------------------------------- lift-ty T ⟨ [ c₂ , w₂ ] , γ₂ ⟩
                  |                                                  
                  | lift-ty T ⟪ [ hom-id C {c₁} , g ] , eγ-decompnˡ Γ eγ ⟫_
                  ↓ 
    lift-ty T ⟨ [ c₁ , w­₁ ] , γ₁ ⟩

                                                                                      lift-ty-mor-C f refl
    ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₂ , Γ ⟪ [ f , hom-id W ] ⟫ γ₂ ⟩ ←------------------- ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₂ , γ₂ ⟩ ∋ t
                                      |                           
                                      | lift-ty-mor-W g (eγ-decompnˡ Γ eγ)
                                      ↓
    ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₁ , γ₁ ⟩ 
                    
  -}
  lift-ty-mor : {c₁ c₂ : Ob C} {w₁ w₂ : Ob W} →
                (f : Hom C c₁ c₂) (g : Hom W w₁ w₂) →
                {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} → 
                (eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁) → 
                lift-ty-obj [ c₂ , w₂ ] γ₂ → lift-ty-obj [ c₁ , w₁ ] γ₁
  lift-ty-mor f g eγ t = lift-ty-mor-W g (eγ-decompnˡ Γ eγ) (lift-ty-mor-C f refl t)


  --------------------------------------------------
  -- Proof of `ty-cong`
  
  {-
    S₁ = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ 
    S₂ = ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
    ψ₁ = lift-ty T ⟪ [ f₁ , hom-id W {w₂} , refl ⟫_
    ϕ₁ = lift-ty T ⟪ [ hom-id C {c₁} , g₁ ] , eγ-decompnˡ Γ eγ₁ ⟫_
    ψ₂ = lift-ty T ⟪ [ f₂ , hom-id W {w₂} , refl ⟫_
    ϕ₂ = lift-ty T ⟪ [ hom-id C {c₁} , g₂ ] , eγ-decompnˡ Γ eγ₂ ⟫_
    ▢ = ty-ctx-subst S₁ (eq (≅ˢ-cong-const-substˡ f₁=f₂) γ₂) 
      = T ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ) {w₂} {func (Γ ˢ⟪ f₁ ⟫ˡ) γ₂}) (eq (≅ˢ-cong-const-substˡ f₁=f₂) {w₂} γ₂) ⟫_

                                    ψ₁
    t ∈ S₂ ⟨ w₂ , γ₂ ⟩ -------------------------→ S₁ ⟨ w₂ , func (Γ ˢ⟪ f₁ ⟫ˡ) γ₂ ⟩
            |                                       ̷↗                   |
            |                                    ̷ ̷                      |       
            |                                 ̷ ̷                         | 
            |                              ̷ ̷                            |                                 
        ψ₂  |                        ▢  ̷ ̷ ▢⁻¹                           | ϕ₁
            |                        ̷ ̷                                  |
            |                     ̷ ̷                                     |
            |                  ̷ ̷                                        |
            |               ̷ ̷                                           |                                        
            ↓           ↙ ̷                                              ↓
          S₁ ⟨ w₂ , func (Γ ˢ⟪ f₂ ⟫ˡ) γ₂ ⟩ -------------------------→ S₁ ⟨ w₁ , γ₁ ⟩
                                                        ϕ₂
  -}
  lift-ty-cong-W : {c : Ob C} {w₁ w₂ : Ob W} →
                   {g g' : Hom W w₁ w₂} (g=g' : g ≡ g') → 
                   {γ₂ γ₂' : Γ ⟨ c ⟩ˡ ⟨ w₂ ⟩} (γ₂=γ₂' : γ₂ ≡ γ₂') → 
                   {γ₁ : Γ ⟨ c ⟩ˡ ⟨ w₁ ⟩} → 
                   {eγ : Γ ⟨ c ⟩ˡ ⟪ g ⟫ γ₂ ≡ γ₁} {eγ' : Γ ⟨ c ⟩ˡ ⟪ g' ⟫ γ₂' ≡ γ₁} →
                   {t : lift-ty-obj [ c , w₂ ] γ₂} → 
                   lift-ty-mor-W g' eγ' (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ γ₂=γ₂' t) ≡ lift-ty-mor-W g eγ t
  lift-ty-cong-W refl refl = trans (sym (ty-comp ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩))
                                        (ty-cong ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (trans (hom-idˡ W) (sym refl)))

  lift-ty-cong-C : {c₁ c₂ : Ob C} {w : Ob W} → 
                   {f f' : Hom C c₁ c₂} (f=f' : f ≡ f') → 
                   {γ₂ : Γ ⟨ w ⟩ʳ ⟨ c₂ ⟩} → 
                   {γ₁ γ₁' : Γ ⟨ w ⟩ʳ ⟨ c₁ ⟩} (γ₁=γ₁' : γ₁ ≡ γ₁') →
                   {eγ : Γ ⟨ w ⟩ʳ ⟪ f ⟫ γ₂ ≡ γ₁} {eγ' : Γ ⟨ w ⟩ʳ ⟪ f' ⟫ γ₂ ≡ γ₁'} →
                   {t : lift-ty-obj [ c₂ , w ] γ₂} →
                   ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ γ₁=γ₁' (lift-ty-mor-C f eγ t) ≡ lift-ty-mor-C f' eγ' t
  lift-ty-cong-C {c₁} {f = f} {f' = f'} refl refl {eγ = eγ} {eγ' = eγ'} {t} =
    begin 
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) refl ⟫ (lift-ty-mor-C f eγ t)
    ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl ⟩
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , ctx-id (Γ ⟨ c₁ ⟩ˡ) ⟫ (lift-ty-mor-C f eγ t)
    ≡⟨ ty-id ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟩
      lift-ty-mor-C f eγ t
    ≡⟨⟩
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) eγ ⟫ _
    ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl ⟩
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) eγ' ⟫ _
    ≡⟨⟩
      lift-ty-mor-C f' eγ' t ∎
    where open ≡-Reasoning

  lift-ty-cong : {c₁ c₂ : Ob C} {w₁ w₂ : Ob W} → 
                 {f f' : Hom C c₁ c₂} {g g' : Hom W w₁ w₂} → 
                 (e-hom : [ f , g ] ≡ [ f' , g' ]) → 
                 {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} → 
                 {eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁} {eγ' : Γ ⟪ [ f' , g' ] ⟫ γ₂ ≡ γ₁} →
                 {t : lift-ty-obj [ c₂ , w₂ ] γ₂} →
                 lift-ty-mor f g eγ t ≡ lift-ty-mor f' g' eγ' t
  lift-ty-cong {f = f} {f'} {g} {g'} e-hom {γ₂} {eγ' = eγ'} = trans (sym (lift-ty-cong-W g=g' γ=γ')) (cong (lift-ty-mor-W g' (eγ-decompnˡ Γ eγ')) (lift-ty-cong-C f=f' γ=γ' ))
    where
      f=f' : f ≡ f'
      f=f' = proj₁ (,-injective e-hom)

      g=g' : g ≡ g'
      g=g' = proj₂ (,-injective e-hom)

      γ=γ' : Γ ⟨ _ ⟩ʳ ⟪ f ⟫ γ₂ ≡ Γ ⟨ _ ⟩ʳ ⟪ f' ⟫ γ₂
      γ=γ' = cong (Γ ⟪_⟫ γ₂) (×-≡,≡→≡ [ f=f' , refl ])


  --------------------------------------------------
  -- Proof of `ty-id`

  lift-ty-id : {c : Ob C} {w : Ob W} {γ : Γ ⟨ [ c , w ] ⟩} {t : lift-ty-obj [ c , w ] γ} → 
               lift-ty-mor (hom-id C) (hom-id W) (ctx-id Γ) t ≡ t
  lift-ty-id {c} {w} {γ} {t} = proof
    where
      open ≡-Reasoning
      lift-ty-id-W : {c : Ob C} {w : Ob W} →
                     {γ γ' : Γ ⟨ c ⟩ˡ ⟨ w ⟩} (γ=γ' : γ ≡ γ') →
                     {eγ : Γ ⟨ c ⟩ˡ ⟪ hom-id W ⟫ γ ≡ γ'} → 
                     {t : lift-ty-obj [ c , w ] γ'} →
                     lift-ty-mor-W (hom-id W) eγ (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (sym γ=γ') t) ≡ t
      lift-ty-id-W {c} refl = trans (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl)
                             (trans (ty-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)
                             (trans (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl)
                                    (ty-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)))
      module _ {c : Ob C} where
        iso₁ : T ᵗʸ⟨ c ⟩ˡ [ lift-ctx Γ ˢ⟪ hom-id C ⟫ˡ ] [ to lift-ctx-naturalˡ ] ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]
        iso₁ = ty-subst-cong-ty (to lift-ctx-naturalˡ) ty-fix-ty-idˡ

        s₁=iso₁ : s₁ (mor-to-↣ˡ T (hom-id C)) ≅ⁿ to iso₁
        s₁=iso₁ = ty-subst-map-cong mor-to-↣-idˡ

        iso₂ : T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ hom-id C ⟫ˡ) ] ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]
        iso₂ = transᵗʸ (symᵗʸ lock-fmap-naturalˡ) iso₁

        s₂=iso₂ : s₂ (mor-to-↣ˡ T (hom-id C)) ≅ⁿ to iso₂
        s₂=iso₂ = ⊙-congʳ (from lock-fmap-naturalˡ) (ty-subst-map-cong mor-to-↣-idˡ)

        iso₃ : ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ hom-id C ⟫ˡ) ] ⟩ ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
        iso₃ = mod-cong μ iso₂

        s₃=iso₃ : s₃ (mor-to-↣ˡ T (hom-id C)) ≅ⁿ to iso₃
        eq s₃=iso₃ s = 
          begin
            func (mod-on-↣ μ (s₂ (mor-to-↣ˡ T (hom-id C)))) s
          ≡⟨ eq (mod-on-↣-cong μ s₂=iso₂) s ⟩
            func (mod-on-↣ μ (to iso₂)) s
          ≡˘⟨ eq (mod-on-↣-comp μ (to iso₁) (from lock-fmap-naturalˡ)) s ⟩ -- NOT PROVED
            func (mod-on-↣ μ (from lock-fmap-naturalˡ)) (func (mod-on-↣ μ (to iso₁)) s)
          ≡⟨ eq (mod-on-↣-mod-cong-from μ lock-fmap-naturalˡ) (func (mod-on-↣ μ (to iso₁)) s) ⟩ -- NOT PROVED
            func (from (mod-cong μ lock-fmap-naturalˡ)) (func (mod-on-↣ μ (to iso₁)) s)
          ≡⟨ cong (func (from (mod-cong μ lock-fmap-naturalˡ))) (eq (mod-on-↣-mod-cong-to μ iso₁) s) ⟩ -- NOT PROVED
            func (from (mod-cong μ lock-fmap-naturalˡ)) (func (to (mod-cong μ iso₁)) s)
          ≡˘⟨ eq (to-eq (mod-cong-sym μ)) (func (to (mod-cong μ iso₁)) s) ⟩
            func (to (mod-cong μ (symᵗʸ lock-fmap-naturalˡ))) (func (to (mod-cong μ iso₁)) s)
          ≡˘⟨ eq (to-eq (mod-cong-trans μ)) s ⟩
            func (to (mod-cong μ iso₂)) s
          ≡⟨⟩
            func (to iso₃) s ∎
          where open ≡-Reasoning

        iso₄ : ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ hom-id C ⟫ˡ ] ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ id-subst (Γ ⟨ c ⟩ˡ) ]
        iso₄ = ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩

        iso₅ : ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ id-subst (Γ ⟨ c ⟩ˡ) ] ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
        iso₅ = ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
          {- func (from (transᵗʸ iso₄ iso₅)) {w} {γ} t
            = func (from (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) 
                  (func (from (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) t)
            = func (from (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) t
            = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (ctx-id Γ) t
            = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , eγ ⟫ t
          -}
          {- func (to (transᵗʸ iso₄ iso₅)) {w} {γ} t
            = func (to (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) 
                  (func (to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) t)
            = func (to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) t
            = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (sym (ctx-id Γ)) t
            = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , ? ⟫ t
            where ? : Γ ⟪ [ hom-id C , hom-id W ] ⟫ γ ≡ Γ ⟪ [ hom-id C , hom-id W ] ⟫ γ
                    ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ refl ⟩
                      ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W , ctx-id Γ ⟨ c ⟩ ⟫ t
                    ≡ ⟨ ty-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟩
                      t
          -}
        
        iso-eq : transᵗʸ (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)) iso₃ ≅ᵉ transᵗʸ iso₄ iso₅
        iso-eq = step₅
          where
            step₁ : transᵗʸ (symᵗʸ lock-fmap-naturalˡ) iso₁ 
                      ≅ᵉ 
                    transᵗʸ (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ])) 
                            (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) _) (ty-subst-id _))
            eq (from-eq step₁) s = 
              begin
                func (from iso₁) (func (to (lock-fmap-naturalˡ {T = T})) s)
              ≡⟨⟩
                func (from (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-idˡ {T = T}))) (func (to (lock-fmap-naturalˡ {T = T})) s)
              ≡⟨ {!   !} ⟩ -- TODO:
              --   func (from (ty-subst-cong-subst (transˢ (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (lock-fmap-id μ)) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]))) s
              -- ≡˘⟨ eq (from-eq (symᵉ (ty-subst-cong-subst-trans {T = T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]}))) s ⟩ -- SLOW 
                func (from (transᵗʸ (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ])) (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ])))) s
              ≡⟨⟩
                func (from (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]))) 
                (func (from (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]))) s)
              ≡⟨⟩
                func (from (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]))) (func (from (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]))) (func (from (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]))) s)) ∎
            
            step₂ : transᵗʸ (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)) iso₃ 
                      ≅ᵉ 
                    transᵗʸ (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)) 
                    (transᵗʸ (mod-cong μ (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ]))) 
                              (mod-cong μ (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) _) (ty-subst-id _))))
            step₂ = transᵗʸ-congʳ {e1 = mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)} (transᵉ (mod-cong-cong μ step₁) (mod-cong-trans μ))

            step₃ : transᵗʸ (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)) iso₃ 
                      ≅ᵉ
                    transᵗʸ (transᵗʸ (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)) (mod-cong μ (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ])))) (mod-cong μ (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) _) (ty-subst-id _)))
            step₃ = transᵉ step₂ (symᵉ transᵗʸ-assoc)

            step₄ : transᵗʸ (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)) iso₃ 
                      ≅ᵉ
                    transᵗʸ (transᵗʸ iso₄ (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ)))) (mod-cong μ (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) _) (ty-subst-id _)))
            step₄ = transᵉ step₃ (transᵗʸ-congˡ {e2 = mod-cong μ (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) _) (ty-subst-id _))} (symᵉ (mod-natural-subst-eq μ ≅ˢ-id-const-substˡ))) 

            step₅ : transᵗʸ (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)) iso₃ 
                      ≅ᵉ
                    transᵗʸ iso₄ iso₅
            step₅ = transᵉ step₄ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ {e1 = iso₄} (mod-natural-id μ)))

      lift-ty-id-C : {c : Ob C} {w : Ob W} → 
                     {γ : Γ ⟨ w ⟩ʳ ⟨ c ⟩} → 
                     {eγ : Γ ⟨ w ⟩ʳ ⟪ hom-id C ⟫ γ ≡ Γ ⟨ w ⟩ʳ ⟪ hom-id C ⟫ γ} → 
                     {t : lift-ty-obj [ c , w ] γ} → 
                     ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (ctx-id Γ) (lift-ty-mor-C (hom-id C) eγ t) ≡ t
      lift-ty-id-C {c = c} {eγ = eγ} {t = t} = trans (cong (func (from (transᵗʸ iso₄ iso₅))) proof) (eq (isoʳ (transᵗʸ iso₄ iso₅)) t)
        where
          proof : lift-ty-mor-C (hom-id C) eγ t ≡ func (to (transᵗʸ iso₄ iso₅)) t
          proof =
            begin
              lift-ty-mor-C (hom-id C) eγ t
            ≡⟨ lift-ty-mor-C-refl ⟩
              func (lift-ty-mor-C-helper (mor-to-↣ˡ T (hom-id C))) t
            ≡⟨ cong (func (to (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)))) (eq s₃=iso₃ t) ⟩
              func (to (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ))) (func (to iso₃) t)
            ≡⟨⟩
              func (to (transᵗʸ (mod-natural μ (Γ ˢ⟪ hom-id C ⟫ˡ)) iso₃)) t
            ≡⟨ eq (to-eq iso-eq) t ⟩
              func (to (transᵗʸ iso₄ iso₅)) t ∎

      eγ : Γ ⟨ c ⟩ˡ ⟪ hom-id W ⟫ (Γ ⟨ w ⟩ʳ ⟪ hom-id C ⟫ γ) ≡ γ
      eγ = eγ-decompnˡ Γ (ctx-id Γ)

      eγ-refl : Γ ⟨ w ⟩ʳ ⟪ hom-id C ⟫ γ ≡ Γ ⟨ w ⟩ʳ ⟪ hom-id C ⟫ γ
      eγ-refl = refl

      proof : lift-ty-mor (hom-id C) (hom-id W) (ctx-id Γ) t ≡ t
      proof = 
        begin
          lift-ty-mor-W (hom-id W) eγ (lift-ty-mor-C (hom-id C) eγ-refl t)
        ≡˘⟨ cong (lift-ty-mor-W (hom-id W) eγ) (ty-ctx-subst-inverseˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩) ⟩
          lift-ty-mor-W (hom-id W) eγ (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (sym (ctx-id Γ)) (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (ctx-id Γ) (lift-ty-mor-C (hom-id C) eγ-refl t)))
        ≡⟨ lift-ty-id-W (ctx-id Γ) ⟩ 
          ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (ctx-id Γ) (lift-ty-mor-C (hom-id C) eγ-refl t)
        ≡⟨ lift-ty-id-C ⟩
          t ∎

  --------------------------------------------------
  -- Proof of `ty-comp`

  lift-ty-comp : {c₁ c₂ c₃ : Ob C} {w₁ w₂ w₃ : Ob W} → 
                 {f : Hom C c₁ c₂} {f' : Hom C c₂ c₃} {g : Hom W w₁ w₂} {g' : Hom W w₂ w₃} →
                 {γ₃ : Γ ⟨ [ c₃ , w₃ ] ⟩} {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} →
                 {eγ-32 : Γ ⟪ [ f' , g' ] ⟫ γ₃ ≡ γ₂} {eγ-21 : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁} →
                 {t : lift-ty-obj [ c₃ , w₃ ] γ₃} →
                 lift-ty-mor (f' ∙[ C ] f) (g' ∙[ W ] g) (strong-ctx-comp Γ eγ-32 eγ-21) t ≡ lift-ty-mor f g eγ-21 (lift-ty-mor f' g' eγ-32 t)
  lift-ty-comp {c₁} {c₂} {c₃} {w₁} {w₂} {w₃} {f} {f'} {g} {g'} {γ₃} {γ₂} {γ₁} {eγ-32} {eγ-21} {t} = proof
    where
      open ≡-Reasoning
      eγ-21' : Γ ⟨ c₁ ⟩ˡ ⟪ g ⟫ (Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂) ≡ γ₁
      eγ-21' = eγ-decompnˡ Γ eγ-21

      eγ-32' : Γ ⟨ c₂ ⟩ˡ ⟪ g' ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃) ≡ γ₂
      eγ-32' = eγ-decompnˡ Γ eγ-32

      eγ-comp : Γ ⟨ c₁ ⟩ˡ ⟪ g' ∙[ W ] g ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ∙[ C ] f ⟫ γ₃) ≡ γ₁
      eγ-comp = eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)
      
      eγ-new : Γ ⟨ c₁ ⟩ˡ ⟪ g' ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃)) ≡ Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂
      eγ-new = ty-subst-new-proof (Γ ˢ⟪ f ⟫ˡ) (eγ-decompnˡ Γ eγ-32)

      -- NOT USED
      eγ-new' : Γ ⟨ c₁ ⟩ˡ ⟪ g' ∙[ W ] g ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃)) ≡ γ₁ 
      eγ-new' = strong-ctx-comp (Γ ⟨ c₁ ⟩ˡ) eγ-new eγ-21'

      iso₁ : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f' ∙[ C ] f ⟫ˡ ] ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] [ Γ ˢ⟪ f' ⟫ˡ ]
      iso₁ = transᵗʸ (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩) 
                     (symᵗʸ (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (Γ ˢ⟪ f ⟫ˡ) (Γ ˢ⟪ f' ⟫ˡ)))
        {- func (from iso₁) {w} {γ} t
          = func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (Γ ˢ⟪ f ⟫ˡ) (Γ ˢ⟪ f' ⟫ˡ))) 
                (func (from (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) {w} {γ} t)
          = func (from (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) {w} {γ} t
          = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (eq (⊚-comp-const-substˡ f f') γ) t
          = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W {w} , eγ ⟫ t
            where 
              eγ = trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) (trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (hom-idˡ D) ])) (ctx-comp Γ))
              eγ : Γ ⟨ c₁ ⟩ˡ ⟪ hom-id W ⟫ (Γ ⟨ w ⟩ʳ ⟪ f' ∙[ C ] f ⟫ γ) ≡ Γ ⟨ w ⟩ʳ ⟪ f ⟫ (Γ ⟨ w ⟩ʳ ⟪ f' ⟫ γ)
        -}
        {- func (to iso₁) {w} {γ} t
          = func (to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩)) {w} {γ} t
          = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (sym (eq (⊚-comp-const-substˡ f f') γ)) t
          = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ hom-id W {w} , eγ ⟫ t
            where
              eγ = trans (ctx-id (Γ ⟨ c₁ ⟩ˡ)) (sym (trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (hom-idˡ D) ])) (ctx-comp Γ)))
              eγ : Γ ⟨ c₁ ⟩ˡ ⟪ hom-id W ⟫ (Γ ⟨ w ⟩ʳ ⟪ f ⟫ (Γ ⟨ w ⟩ʳ ⟪ f' ⟫ γ) ≡ Γ ⟨ w ⟩ʳ ⟪ f' ∙[ C ] f ⟫ γ
        -}

      lift-ty-comp-W : {s : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] [ Γ ˢ⟪ f' ⟫ˡ ] ⟨ w₃ , γ₃ ⟩} →
                       lift-ty-mor-W (g' ∙[ W ] g) eγ-comp (func (to iso₁) s) ≡ lift-ty-mor-W g eγ-21' (lift-ty-mor-W g' eγ-new s)
      lift-ty-comp-W {s} = trans (sym (ty-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩))
                          (trans (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ (hom-idˡ W))
                                 (ty-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩))

      lift-ty-comp-C : lift-ty-mor-C (f' ∙[ C ] f) refl t ≡ func (to iso₁) (lift-ty-mor-C f refl (lift-ty-mor-C f' refl t))
      lift-ty-comp-C = 
        begin
          lift-ty-mor-C (f' ∙[ C ] f) refl t
        ≡⟨ lift-ty-mor-C-refl ⟩
          func (lift-ty-mor-C-helper (mor-to-↣ˡ T (f' ∙[ C ] f))) t
        ≡⟨⟩
          func (to (mod-natural μ (Γ ˢ⟪ f' ∙[ C ] f ⟫ˡ))) (func (s₃ (mor-to-↣ˡ T (f' ∙[ C ] f))) t)
        ≡⟨ {!   !} ⟩ -- TODO: 
          func (to iso₁)
          (func (ty-subst-map (Γ ˢ⟪ f' ⟫ˡ) (lift-ty-mor-C-helper (mor-to-↣ˡ T f))) 
          (func (lift-ty-mor-C-helper (mor-to-↣ˡ T f')) t))
        ≡⟨⟩
          func (to iso₁) 
          (func (lift-ty-mor-C-helper (mor-to-↣ˡ T f)) 
          (func (lift-ty-mor-C-helper (mor-to-↣ˡ T f')) t))
        ≡˘⟨ cong (func (to iso₁)) lift-ty-mor-C-refl ⟩
          func (to iso₁) (lift-ty-mor-C f refl (func (lift-ty-mor-C-helper (mor-to-↣ˡ T f')) t))
        ≡˘⟨ cong (func (to iso₁)) (cong (lift-ty-mor-C f refl) lift-ty-mor-C-refl) ⟩
          func (to iso₁) (lift-ty-mor-C f refl (lift-ty-mor-C f' refl t)) ∎

      {-
        A = ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
        B = ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
        
                                                      func (lift-ty-mor-C-helper (mor-to-↣ˡ T f))
        A [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₃ , Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃ ⟩ ←------------------------------------------ B ⟨ w₃ , Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃ ⟩ ∋ s
                                    |                                                                         |
        A [ Γ ˢ⟪ f ⟫ˡ ] ⟪ g' , _ ⟫_ |                                                                         | B ⟪ g' , _ ⟫_
                                    ↓                                                                         ↓
                        A [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩ ←-------------------------------------------------- B ⟨ w₂ , γ₂ ⟩
                                                        func (lift-ty-mor-C-helper (mor-to-↣ˡ T f))
      -}
      top-left-commutativity : {s : lift-ty-obj [ c₂ , w₃ ] (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃)} → 
                              lift-ty-mor-W g' eγ-new (lift-ty-mor-C f refl s) 
                                ≡ 
                              lift-ty-mor-C f refl (lift-ty-mor-W g' eγ-32' s)
      top-left-commutativity = trans (cong (lift-ty-mor-W g' eγ-new) lift-ty-mor-C-refl)   
                             (trans (_↣_.naturality (lift-ty-mor-C-helper (mor-to-↣ˡ T f)))
                                    (sym lift-ty-mor-C-refl))

      proof = 
        begin
          lift-ty-mor-W (g' ∙[ W ] g) eγ-comp (lift-ty-mor-C (f' ∙[ C ] f) refl t)
        ≡⟨ cong (lift-ty-mor-W (g' ∙[ W ] g) eγ-comp) lift-ty-comp-C ⟩
          lift-ty-mor-W (g' ∙[ W ] g) eγ-comp (func (to iso₁) 
            (lift-ty-mor-C f refl (lift-ty-mor-C f' refl t)))
        ≡⟨ lift-ty-comp-W ⟩
          lift-ty-mor-W g eγ-21' (lift-ty-mor-W g' eγ-new 
            (lift-ty-mor-C f refl (lift-ty-mor-C f' refl t)))
        ≡⟨ cong (lift-ty-mor-W g eγ-21') top-left-commutativity ⟩
          lift-ty-mor-W g eγ-21' (lift-ty-mor-C f refl
            (lift-ty-mor-W g' eγ-32' (lift-ty-mor-C f' refl t))) ∎

lift-ty : Ty (lift-ctx Γ) → Ty Γ
lift-ty T ⟨ [ c , w ] , γ ⟩ = lift-ty-obj T [ c , w ] γ
(lift-ty T) ⟪ [ f , g ] , eγ ⟫ t = lift-ty-mor T f g eγ t
ty-cong (lift-ty T) e-hom = lift-ty-cong T e-hom
ty-id (lift-ty T) = lift-ty-id T
ty-comp (lift-ty T) = lift-ty-comp T


--------------------------------------------------
-- Properties of ⟨ μ̃ ∣ _ ⟩

-- Proof of `Modality.mod-cong`
lift-ty-mod-cong : {Γ : Ctx C×W} {T S : Ty (lift-ctx Γ)} → T ≅ᵗʸ S → lift-ty T ≅ᵗʸ lift-ty S
func (from (lift-ty-mod-cong T=S)) {[ c , w ]} {γ} = func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c)))) {w} {γ}
  {-
    lift-ctx Γ ⟨ c ⟩ˡ ⊢ ty-fix-ty-congˡ T=S c : T ᵗʸ⟨ c ⟩ˡ ≅ᵗʸ S ᵗʸ⟨ c ⟩ˡ
    Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⊢ ty-subst-cong-ty (to lift-ctx-naturalˡ) _ : T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ≅ᵗʸ S ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] 
    Γ ⟨ c ⟩ˡ ⊢ mod-cong μ _ : ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ≅ᵗʸ ⟨ μ ∣ S ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
  -}
_↣_.naturality (from (lift-ty-mod-cong {Γ} {T} {S} T=S)) {[ c₁ , w₁ ]} {[ c₂ , w₂ ]} {[ f , g ]} {γ₂} {γ₁} {eγ} {t} = proof
  {-
                                    lift-ty T ⟪ [ f , g ] , eγ ⟫_
    lift-ty T ⟨ [ c₁ , w₁ ] , γ₁ ⟩ ←----------------------------- lift-ty T ⟨ [ c₂ , w₂ ] , γ₂ ⟩ ∋ t
                |                                                                   |                  
                | func from {[ c₁ , w₁ ]} {γ₁}         func from {[ c₂ , w₂ ]} {γ₂} |
                ↓                                                                   ↓
    lift-ty S ⟨ [ c₁ , w₁ ] , γ₁ ⟩ ←----------------------------- lift-ty S ⟨ [ c₂ , w₂ ] , γ₂ ⟩
                                    lift-ty S ⟪ [ f , g ] , eγ ⟫_
  -}
  where
    open ≡-Reasoning
    {-
                                              ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ g , _ ⟫_
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₁ , γ₁ ⟩ ←----------------- ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩
                                      |                                                                             |
                                      | func from                                                         func from | 
                                      ↓                                                                             ↓
      ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₁ , γ₁ ⟩ ←----------------- ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩
                                              ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟪ g , _ ⟫_
    -}
    commutativity₁ : {s : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩} → 
                   lift-ty-mor-W S g (eγ-decompnˡ Γ eγ) (func (from (lift-ty-mod-cong T=S)) s) ≡ func (from (lift-ty-mod-cong T=S)) (lift-ty-mor-W T g (eγ-decompnˡ Γ eγ) s)
    commutativity₁ {s} = _↣_.naturality (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))) 

    {-
                                                                      func (to (mod-natural μ (Γ ˢ⟪ f ⟫ˡ)))
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩ ←----------------- ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap (Γ ˢ⟪ f ⟫ˡ ]) ⟩ ⟨ w₂ , γ₂ ⟩
                                      |                                                                                           |
                                      | func from                                                        func (to (mod-cong μ _)) |
                                      ↓                                                                                           ↓
      ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ Γ ˢ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩ ←----------------- ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap (Γ ˢ⟪ f ⟫ˡ ]) ⟩ ⟨ w₂ , γ₂ ⟩
                                                                      func (to (mod-natural μ (Γ ˢ⟪ f ⟫ˡ)))                     
    -}
    iso₁ : S ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ] ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ]
    iso₁ = ty-subst-cong-ty (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) (symᵗʸ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))

    commutativity₂ : {s : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (Γ ˢ⟪ f ⟫ˡ) ] ⟩ ⟨ w₂ , γ₂ ⟩} → 
                   func (to (mod-natural μ (Γ ˢ⟪ f ⟫ˡ))) (func (to (mod-cong μ iso₁)) s) ≡ func (from (lift-ty-mod-cong T=S)) (func (to (mod-natural μ (Γ ˢ⟪ f ⟫ˡ))) s)
    commutativity₂ {s} = {! !} -- FIXME: eq (to-eq (mod-natural-ty-eq μ (Γ ˢ⟪ f ⟫ˡ) (symᵗʸ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁))))) s

    {-
                                                                                         func (s₃ (mor-to-↣ˡ T f))
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap (Γ ˢ⟪ f ⟫ˡ ]) ⟩ ⟨ w₂ , γ₂ ⟩ ←----------------- ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₂ , γ₂ ⟩
                                                |                                                                                             |
                                                | func (to (mod-cong μ _))                                                          func from |
                                                ↓                                                                                             ↓
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap (Γ ˢ⟪ f ⟫ˡ ]) ⟩ ⟨ w₂ , γ₂ ⟩ ←----------------- ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w₂ , γ₂ ⟩
                                                                                         func (s₃ (mor-to-↣ˡ T f))
    -}
    commutativity₃ : func (s₃ (mor-to-↣ˡ S f)) (func (from (lift-ty-mod-cong T=S)) t) ≡ func (to (mod-cong μ iso₁)) (func (s₃ (mor-to-↣ˡ T f)) t)
    commutativity₃ = 
      begin
        func (mod-on-↣ μ (s₂ (mor-to-↣ˡ S f))) (func (from (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₂)))) t)
      ≡˘⟨ cong (func (mod-on-↣ μ (s₂ (mor-to-↣ˡ S f)))) (eq (mod-on-↣-mod-cong-from μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₂))) t) ⟩
        func (mod-on-↣ μ (s₂ (mor-to-↣ˡ S f))) (func (mod-on-↣ μ (from (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₂)))) t)
      ≡⟨ {!   !} ⟩ -- FIXME: eq (mod-on-↣-comp μ (from (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₂))) (s₂ (mor-to-↣ˡ S f)))
        func (mod-on-↣ μ (s₂ (mor-to-↣ˡ S f) ⊙ from (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₂)))) t
      ≡⟨ {!  !} ⟩ -- TODO: 
        func (mod-on-↣ μ (to iso₁ ⊙ s₂ (mor-to-↣ˡ T f))) t
      ≡˘⟨ eq (mod-on-↣-comp μ (s₂ (mor-to-↣ˡ T f)) (to iso₁)) t ⟩
        func (mod-on-↣ μ (to iso₁)) (func (mod-on-↣ μ (s₂ (mor-to-↣ˡ T f))) t)
      ≡⟨ eq (mod-on-↣-mod-cong-to μ iso₁) (func (s₃ (mor-to-↣ˡ T f)) t) ⟩
        func (to (mod-cong μ (ty-subst-cong-ty (lock-fmap μ (Γ ˢ⟪ f ⟫ˡ)) 
                                                (symᵗʸ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c₁)))))) 
          (func (s₃ (mor-to-↣ˡ T f)) t) ∎
    proof = {!   !} -- COMBINE commutativity₁, commutativity₂, AND commutativity₃
func (to (lift-ty-mod-cong T=S)) {[ c , w ]} {γ} = func (to (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c)))) {w} {γ}
_↣_.naturality (to (lift-ty-mod-cong T=S)) = {!   !}
eq (isoˡ (lift-ty-mod-cong T=S)) {[ c , w ]} t = eq (isoˡ (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c)))) t
eq (isoʳ (lift-ty-mod-cong T=S)) {[ c , w ]} t = eq (isoʳ (mod-cong μ (ty-subst-cong-ty (to lift-ctx-naturalˡ) (ty-fix-ty-congˡ T=S c)))) t












--------------------------------------------------
-- Proof of `Modality.mod-natural`

fix-ty-lock-fmap-naturalˡ : (σ : Δ ⇒ Γ) {T : Ty (lift-ctx Γ)} {c : Ob C} → 
  (T [ lift-subst σ ]) ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ]
fix-ty-lock-fmap-naturalˡ σ {T} {c} = {!   !}

lift-ty-mod-natural : (σ : Δ ⇒ Γ) {T : Ty (lift-ctx Γ)} →
                      (lift-ty T) [ σ ] ≅ᵗʸ lift-ty (T [ lift-subst σ ])
-- from : (lift-ty T) [ σ ] ↣ lift-ty (T [ lift-subst σ ])
func (from (lift-ty-mod-natural σ)) {[ c , _ ]} = func (to (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ {c = c})) ⊙ from (mod-natural μ (σ ˢ⟨ c ⟩ˡ)))
{-
    ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ σ ˢ⟨ c ⟩ˡ ]
  ↣ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ] ⟩
  = from (mod-natural μ (σ ˢ⟨ c ⟩ˡ)) 

    ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ] ⟩ ⟨ w , γ ⟩
  → ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ ⟨ w , γ ⟩
  = to (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))
-}
_↣_.naturality (from (lift-ty-mod-natural σ {T})) {[ c₁ , w₁ ]} {[ c₂ , w₂ ]} {[ f , g ]} {γ₂} {γ₁} {eγ} {t} = {!   !}
-- to : lift-ty (T [ lift-subst σ ]) ↣ (lift-ty T) [ σ ]
func (to (lift-ty-mod-natural σ {T})) {[ c , _ ]} = func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ)) ⊙ from (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ)))
{-
    ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩
  ↣ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ] ⟩
  = from (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))
    ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ] ⟩
  ↣ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ to lift-ctx-naturalˡ ] ⟩ [ σ ˢ⟨ c ⟩ˡ ]
  = to (mod-natural μ (σ ˢ⟨ c ⟩ˡ))
-}
_↣_.naturality (to (lift-ty-mod-natural σ {T})) = {!   !} 
-- isoˡ : to ⊙ from ≅ⁿ id-trans T
eq (isoˡ (lift-ty-mod-natural σ)) {[ c , _ ]} t = trans (cong (func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ)))) 
                                                                  (eq (isoʳ (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))) (func (from (mod-natural μ (σ ˢ⟨ c ⟩ˡ))) t))) 
                                                        (eq (isoˡ (mod-natural μ (σ ˢ⟨ c ⟩ˡ))) t)
-- isoʳ : from ⊙ to ≅ⁿ id-trans S
eq (isoʳ (lift-ty-mod-natural σ {T})) {[ c , w ]} t = trans (cong (func (to (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ)))) 
                                                                  (eq (isoʳ (mod-natural μ (σ ˢ⟨ c ⟩ˡ))) (func (from (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))) t))) 
                                                            (eq (isoˡ (mod-cong μ (fix-ty-lock-fmap-naturalˡ σ))) t)
