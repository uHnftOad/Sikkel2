--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
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
-- ⟨ μ̃ ∣ _ ⟩

lift-ctx-const-subst-natural-helperˡ : {Γ : Ctx C×W} {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} → 
                                        lift-ctx Γ ⟪ f ⟫ˡ ⊚ to lift-ctx-naturalˡ ≅ˢ to lift-ctx-naturalˡ ⊚ lock-fmap μ (Γ ⟪ f ⟫ˡ)
eq (lift-ctx-const-subst-natural-helperˡ {Γ} {c₁}) γ = ctx-id (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩)

lift-ctx-const-subst-naturalˡ : {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} → 
                                 T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ⟪ f ⟫ˡ ] [ ⇆ ] ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ]
lift-ctx-const-subst-naturalˡ {Γ} {T} {c₁} {f = f} = transᵗʸ (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) (lift-ctx Γ ⟪ f ⟫ˡ) ⇆) 
                                                     (transᵗʸ (ty-subst-cong-subst lift-ctx-const-subst-natural-helperˡ (T ᵗʸ⟨ c₁ ⟩ˡ)) 
                                                               (symᵗʸ (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) ⇆ (lock-fmap μ (Γ ⟪ f ⟫ˡ)))))
  {-
      from lift-ctx-const-subst-naturalˡ
    = to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) ⇆ (lock-fmap μ (Γ ⟪ f ⟫ˡ))) ⊙
      from (ty-subst-cong-subst lift-ctx-const-subst-natural-helperˡ (T ᵗʸ⟨ c₁ ⟩ˡ)) ⊙
      from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ) (lift-ctx Γ ⟪ f ⟫ˡ) ⇆)

      func (from lift-ctx-const-subst-naturalˡ) t = ty-ctx-subst (T ᵗʸ⟨ c₁ ⟩ˡ) (ctx-id (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩)) t
  -}

lift-ctx-fix-subst-natural-helperˡ : {Δ Γ : Ctx C×W} {σ : Δ ⇒ Γ} {c : Ob C} → 
                                      lift-subst σ ˢ⟨ c ⟩ˡ ⊚ ⇆ ≅ˢ ⇆ ⊚ lock-fmap μ (σ ˢ⟨ c ⟩ˡ)
eq lift-ctx-fix-subst-natural-helperˡ γ = refl

lift-ctx-fix-subst-naturalˡ : {Δ Γ : Ctx C×W} {σ : Δ ⇒ Γ} {T : Ty (lift-ctx Γ)} {c : Ob C} →
                            T ᵗʸ⟨ c ⟩ˡ [ lift-subst σ ˢ⟨ c ⟩ˡ ] [ ⇆ ] ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ]
lift-ctx-fix-subst-naturalˡ {σ = σ} {T} {c} = transᵗʸ (ty-subst-comp (T ᵗʸ⟨ c ⟩ˡ) (lift-subst σ ˢ⟨ c ⟩ˡ) ⇆) 
                                             (transᵗʸ (ty-subst-cong-subst lift-ctx-fix-subst-natural-helperˡ (T ᵗʸ⟨ c ⟩ˡ)) 
                                                       (symᵗʸ (ty-subst-comp (T ᵗʸ⟨ c ⟩ˡ) ⇆ (lock-fmap μ (σ ˢ⟨ c ⟩ˡ)))))
  {-
    lift-ctx Γ ⟨ c ⟩ˡ ⊢ 
      func (from lift-ctx-fix-subst-naturalˡ) t = func (from (ty-subst-cong-subst lift-ctx-fix-subst-natural-helperˡ (T ᵗʸ⟨ c ⟩ˡ))) t = ty-ctx-subst (T ᵗʸ⟨ c ⟩ˡ) refl t 
      func (to lift-ctx-fix-subst-naturalˡ) t = func (to (ty-subst-cong-subst lift-ctx-fix-subst-natural-helperˡ (T ᵗʸ⟨ c ⟩ˡ))) t = ty-ctx-subst (T ᵗʸ⟨ c ⟩ˡ) refl t
  -}

module _ {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} (η : T ᵗʸ⟨ c₂ ⟩ˡ ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ⟪ f ⟫ˡ ]) where
  η₁ : T ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ⟪ f ⟫ˡ ] [ ⇆ ]
  η₁ = ty-subst-map ⇆ η
  
  η₂ : T ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ]
  η₂ = from lift-ctx-const-subst-naturalˡ ⊙ η₁
    {-
      func (η₂ (mor-to-↣ˡ T f)) = ty-ctx-subst (T ᵗʸ⟨ c₁ ⟩ˡ) (ctx-id (Γ ⟨ c₁ ⟩ˡ ,lock⟨ μ ⟩)) (func (mor-to-↣ˡ T f) s)
    -}

  η₃ : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ⟩ ↣ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] ⟩
  η₃ = mod-cong' μ η₂

  η₄ : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ⟩ ↣ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ]
  η₄ = to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ η₃

{-
  Γ @ C×W
  lift-ctx Γ ⊢ T type @ C×V
  -----------------------------------------
  lift-ctx Γ ⟨ c ⟩ˡ ⊢ T ᵗʸ⟨ c ⟩ˡ type @ V
  Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⊢ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] type @ V
  ----------------------------------------------------------------------
  Γ ⟨ c ⟩ˡ ⊢ ⟨ μ | T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ type @ W
-}
module _ {Γ : Ctx C×W} (T : Ty (lift-ctx Γ)) where
  lift-ty-obj : (cw : Ob C×W) → (γ : Γ ⟨ cw ⟩) → Set
  lift-ty-obj [ c , w ] γ = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ ⟨ w , γ ⟩

  -- ⟨ μ̃ ∣ T ⟩ ⟪ [ hom-id C , g ] , _ ⟫_ 
  lift-ty-mor-W : {c : Ob C} {w₁ w₂ : Ob W} → 
                  (g : Hom W w₁ w₂) →
                  {γ₂ : Γ ⟨ c ⟩ˡ ⟨ w₂ ⟩} {γ₁ : Γ ⟨ c ⟩ˡ ⟨ w₁ ⟩} → 
                  (eγ : Γ ⟨ c ⟩ˡ ⟪ g ⟫ γ₂ ≡ γ₁) → 
                  lift-ty-obj [ c , w₂ ] γ₂ → lift-ty-obj [ c , w₁ ] γ₁
  lift-ty-mor-W g eγ = ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , eγ ⟫_

  -- ⟨ μ̃ ∣ T ⟩ ⟪ [ f , hom-id W ] , refl ⟫_
  lift-ty-mor-C : {c₁ c₂ : Ob C} {w : Ob W} (f : Hom C c₁ c₂) {γ₂ : Γ ⟨ w ⟩ʳ ⟨ c₂ ⟩} → 
                  lift-ty-obj [ c₂ , w ] γ₂ → lift-ty-obj [ c₁ , w ] (Γ ⟨ w ⟩ʳ ⟪ f ⟫ γ₂)
  lift-ty-mor-C f = func (η₄ (mor-to-↣ˡ T f))
  
  {- 
    ⟨ μ̃ ∣ T ⟩ ⟪ [ f , g ] , _ ⟫_ 

                                                   lift-ty T ⟪ [ f , hom-id W {w₂} ] , refl ⟫_
    lift-ty T ⟨ [ c₁ , w₂ ] , Γ ⟨ w ⟩ʳ ⟪ f ⟫ γ₂ ⟩ ←------------------------------------------- lift-ty T ⟨ [ c₂ , w₂ ] , γ₂ ⟩
                  |                                                  
                  | lift-ty T ⟪ [ hom-id C {c₁} , g ] , eγ-decompnˡ Γ eγ ⟫_
                  ↓ 
    lift-ty T ⟨ [ c₁ , w­₁ ] , γ₁ ⟩

                                                          lift-ty-mor-C f
    ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩ ←---------------- ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ⟩ ⟨ w₂ , γ₂ ⟩ ∋ t
                  |                           
                  | lift-ty-mor-W g (eγ-decompnˡ Γ eγ)
                  ↓
    ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟨ w₁ , γ₁ ⟩ 
                    
  -}
  lift-ty-mor : {c₁ c₂ : Ob C} {w₁ w₂ : Ob W} →
                (f : Hom C c₁ c₂) (g : Hom W w₁ w₂) →
                {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} → 
                (eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁) → 
                lift-ty-obj [ c₂ , w₂ ] γ₂ → lift-ty-obj [ c₁ , w₁ ] γ₁
  lift-ty-mor f g eγ t = lift-ty-mor-W g (eγ-decompnˡ Γ eγ) (lift-ty-mor-C f t)
  
  lift-ty-cong : {c₁ c₂ : Ob C} {w₁ w₂ : Ob W} → 
                 {f f' : Hom C c₁ c₂} {g g' : Hom W w₁ w₂} → 
                 (e-hom : [ f , g ] ≡ [ f' , g' ]) → 
                 {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} → 
                 {eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁} {eγ' : Γ ⟪ [ f' , g' ] ⟫ γ₂ ≡ γ₁} →
                 {t : lift-ty-obj [ c₂ , w₂ ] γ₂} →
                 lift-ty-mor f g eγ t ≡ lift-ty-mor f' g' eγ' t
  lift-ty-cong {c₁} {w₂ = w₂} {f} {f'} {g} {g'} e-hom {γ₂} {γ₁} {eγ' = eγ'} {t} = trans (sym (lift-ty-cong-W g=g' γ=γ')) (cong (lift-ty-mor-W g' (eγ-decompnˡ Γ eγ')) (lift-ty-cong-C f=f' γ=γ'))
    where
      open ≡-Reasoning
      lift-ty-cong-W : (g=g' : g ≡ g') → 
                       {γ₂ γ₂' : Γ ⟨ c₁ ⟩ˡ ⟨ w₂ ⟩} (γ₂=γ₂' : γ₂ ≡ γ₂') → 
                       {eγ : Γ ⟨ c₁ ⟩ˡ ⟪ g ⟫ γ₂ ≡ γ₁} {eγ' : Γ ⟨ c₁ ⟩ˡ ⟪ g' ⟫ γ₂' ≡ γ₁} →
                       {t : lift-ty-obj [ c₁ , w₂ ] γ₂} → 
                       lift-ty-mor-W g' eγ' (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ γ₂=γ₂' t) ≡ lift-ty-mor-W g eγ t
      lift-ty-cong-W refl refl = trans (sym (ty-comp ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ] ⟩))
                                            (ty-cong ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ] ⟩ (trans (hom-idˡ W) (sym refl)))

      lift-ty-cong-C : (f=f' : f ≡ f') → 
                       (γ₁=γ₁' : Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂ ≡ Γ ⟨ w₂ ⟩ʳ ⟪ f' ⟫ γ₂) →
                       ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ γ₁=γ₁' (lift-ty-mor-C f t) ≡ lift-ty-mor-C f' t 
      lift-ty-cong-C refl γ₁=γ₁' = trans (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ refl) (ty-id ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩)
        
      f=f' : f ≡ f'
      f=f' = proj₁ (,-injective e-hom)

      g=g' : g ≡ g'
      g=g' = proj₂ (,-injective e-hom)

      γ=γ' : Γ ⟨ _ ⟩ʳ ⟪ f ⟫ γ₂ ≡ Γ ⟨ _ ⟩ʳ ⟪ f' ⟫ γ₂
      γ=γ' = cong (Γ ⟪_⟫ γ₂) (×-≡,≡→≡ [ f=f' , refl ])

  lift-ty-id : {c : Ob C} {w : Ob W} {γ : Γ ⟨ [ c , w ] ⟩} {t : lift-ty-obj [ c , w ] γ} → 
               lift-ty-mor (hom-id C) (hom-id W) (ctx-id Γ) t ≡ t
  lift-ty-id {c} {w} {t = t} = proof
    where
      open ≡-Reasoning
      iso : {c : Ob C} → ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ hom-id C ⟫ˡ ] ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ [ id-subst (Γ ⟨ c ⟩ˡ) ]
      iso = ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ] ⟩

      ↣-eq : to (ty-subst-cong-subst (lock-fmap-cong μ (symˢ ≅ˢ-id-const-substˡ)) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])) ⊙ (from lift-ctx-const-subst-naturalˡ ⊙ ty-subst-map ⇆ (mor-to-↣ˡ T (hom-id C)))
               ≅ⁿ
             to (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])))
      eq ↣-eq s = trans (sym (trans (ty-comp T) (ty-comp T))) (ty-cong T (×-≡,≡→≡ [ trans (hom-idˡ C) (hom-idˡ C) , trans (hom-idˡ V) (hom-idˡ V) ]))
      
      proof = 
        begin
          ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ ⟪ hom-id W , eγ-decompnˡ Γ (ctx-id Γ) ⟫ (lift-ty-mor-C (hom-id C) t)
        ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ refl ⟩
          ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ (ctx-id (Γ ⟨ w ⟩ʳ)) (lift-ty-mor-C (hom-id C) t)
        ≡˘⟨ cong (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ (ctx-id (Γ ⟨ w ⟩ʳ))) (eq (isoˡ iso) _) ⟩
          ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ (ctx-id (Γ ⟨ w ⟩ʳ)) (func (to iso) (func (from iso) (lift-ty-mor-C (hom-id C) t)))
        ≡⟨ ty-ctx-subst-inverseʳ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩ ⟩
          func (from (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩)) 
            (func (to (mod-natural μ (Γ ⟪ hom-id C ⟫ˡ)))
              (func (η₃ (mor-to-↣ˡ T (hom-id C))) t))
        ≡˘⟨ eq (to-eq (ty-subst-cong-subst-sym {T = ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩} {ε = ≅ˢ-id-const-substˡ})) _ ⟩
          func (to (ty-subst-cong-subst (symˢ ≅ˢ-id-const-substˡ) ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩)) 
            (func (to (mod-natural μ (Γ ⟪ hom-id C ⟫ˡ)))
              (func (η₃ (mor-to-↣ˡ T (hom-id C))) t))
        ≡⟨ eq (to-eq (mod-natural-subst-eq μ (symˢ ≅ˢ-id-const-substˡ))) _ ⟩
          func (to (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ)))) 
            (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-cong μ (symˢ ≅ˢ-id-const-substˡ)) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])))) 
              (func (η₃ (mor-to-↣ˡ T (hom-id C))) t))
        ≡˘⟨ cong (func (to (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ))))) (eq (mod-cong-trans' μ) t) ⟩
          func (to (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ)))) 
            (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-cong μ (symˢ ≅ˢ-id-const-substˡ)) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])) ⊙ (from lift-ctx-const-subst-naturalˡ ⊙ ty-subst-map ⇆ (mor-to-↣ˡ T (hom-id C))))) t)
        ≡⟨ cong (func (to (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ))))) (eq (mod-cong-cong' μ ↣-eq) t) ⟩
          func (to (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ)))) 
            (func (mod-cong' μ (to (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ]))))) t)
        ≡⟨ eq (to-eq (mod-natural-id μ)) t ⟩
          func (to (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩)) t
        ≡⟨⟩
          t ∎

  lift-ty-comp : {c₁ c₂ c₃ : Ob C} {w₁ w₂ w₃ : Ob W} → 
                 {f : Hom C c₁ c₂} {f' : Hom C c₂ c₃} {g : Hom W w₁ w₂} {g' : Hom W w₂ w₃} →
                 {γ₃ : Γ ⟨ [ c₃ , w₃ ] ⟩} {γ₂ : Γ ⟨ [ c₂ , w₂ ] ⟩} {γ₁ : Γ ⟨ [ c₁ , w₁ ] ⟩} →
                 {eγ-32 : Γ ⟪ [ f' , g' ] ⟫ γ₃ ≡ γ₂} {eγ-21 : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁} →
                 {t : lift-ty-obj [ c₃ , w₃ ] γ₃} →
                 lift-ty-mor (f' ∙[ C ] f) (g' ∙[ W ] g) (strong-ctx-comp Γ eγ-32 eγ-21) t ≡ lift-ty-mor f g eγ-21 (lift-ty-mor f' g' eγ-32 t)
  lift-ty-comp {c₁} {c₂} {c₃} {w₁} {w₂} {w₃} {f} {f'} {g} {g'} {γ₃} {γ₂} {γ₁} {eγ-32} {eγ-21} {t} = trans (cong (lift-ty-mor-W (g' ∙[ W ] g) eγ-comp) (eq lift-ty-comp-C t)) (trans lift-ty-comp-W (cong (lift-ty-mor-W g eγ-21') (_↣_.naturality (η₄ (mor-to-↣ˡ T f)))))
    where
      eγ-21' : Γ ⟨ c₁ ⟩ˡ ⟪ g ⟫ (Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂) ≡ γ₁
      eγ-21' = eγ-decompnˡ Γ eγ-21

      eγ-32' : Γ ⟨ c₂ ⟩ˡ ⟪ g' ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃) ≡ γ₂
      eγ-32' = eγ-decompnˡ Γ eγ-32

      eγ-comp : Γ ⟨ c₁ ⟩ˡ ⟪ g' ∙[ W ] g ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ∙[ C ] f ⟫ γ₃) ≡ γ₁
      eγ-comp = eγ-decompnˡ Γ (strong-ctx-comp Γ eγ-32 eγ-21)
      
      eγ-new : Γ ⟨ c₁ ⟩ˡ ⟪ g' ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f ⟫ (Γ ⟨ w₃ ⟩ʳ ⟪ f' ⟫ γ₃)) ≡ Γ ⟨ w₂ ⟩ʳ ⟪ f ⟫ γ₂
      eγ-new = ty-subst-new-proof (Γ ⟪ f ⟫ˡ) (eγ-decompnˡ Γ eγ-32)

      iso : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f' ∙[ C ] f ⟫ˡ ] ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] [ Γ ⟪ f' ⟫ˡ ]
      iso = transᵗʸ (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) 
                     (symᵗʸ (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))
        {- 
          func (from iso) {w} {γ} t = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (eq (⊚-comp-const-substˡ f f') γ) t
          func (to iso) {w} {γ} t = ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (sym (eq (⊚-comp-const-substˡ f f') γ)) t
        -}

      lift-ty-comp-W : {s : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] [ Γ ⟪ f' ⟫ˡ ] ⟨ w₃ , γ₃ ⟩} →
                       lift-ty-mor-W (g' ∙[ W ] g) eγ-comp (func (to iso) s) ≡ lift-ty-mor-W g eγ-21' (lift-ty-mor-W g' eγ-new s)
      lift-ty-comp-W = trans (sym (ty-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩))
                      (trans (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (hom-idˡ W))
                             (ty-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩))

      lift-ty-comp-C : η₄ (mor-to-↣ˡ T (f' ∙[ C ] f)) ≅ⁿ (to iso) ⊙ (ty-subst-map (Γ ⟪ f' ⟫ˡ) (η₄ (mor-to-↣ˡ T f))) ⊙ (η₄ (mor-to-↣ˡ T f'))
      lift-ty-comp-C = proof
        where
          commutativity₁ : to (mod-natural μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ)) ≅ⁿ to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])))
          commutativity₁ = symⁿ (transⁿ (⊙-congˡ _ (to-eq (mod-natural-subst-eq μ (⊚-comp-const-substˡ f f'))))
                                (transⁿ (⊙-assoc _ _ _)
                                (transⁿ (⊙-congʳ _ (isoˡ (mod-cong μ (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])))))
                                        (id-trans-unitʳ (to (mod-natural μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ)))))))
            {-
              begin
                to (mod-natural μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ))
              ≅˘⟨ id-trans-unitʳ (to (mod-natural μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ))) ⟩
                to (mod-natural μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ)) ⊙ id-trans ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ) ] ⟩
              ≅˘⟨ ⊙-congʳ _ (isoˡ (mod-cong μ (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])))) ⟩
                to (mod-natural μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ)) ⊙ (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
              ≅˘⟨ ⊙-assoc _ _ _ ⟩ 
                to (mod-natural μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ)) ⊙ mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])))
              ≅˘⟨ ⊙-congˡ _ (to-eq (mod-natural-subst-eq μ (⊚-comp-const-substˡ f f'))) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ∎
              where open ≅ⁿ-Reasoning
            -}

          commutativity₂ : from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) 
                             ≅ⁿ 
                           to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                           mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                           mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                           from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                           from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
          commutativity₂ = transⁿ (symⁿ (id-trans-unitˡ _))
                          (transⁿ (symⁿ (⊙-congˡ _ (isoˡ (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)))))
                          (transⁿ (⊙-assoc _ _ _)
                          (transⁿ (symⁿ (⊙-congʳ _ (id-trans-unitˡ _)))
                          (transⁿ (symⁿ (⊙-congʳ _ (⊙-congˡ _ (isoˡ (mod-cong μ (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])))))))
                          (transⁿ (⊙-congʳ _ (⊙-assoc _ _ _))
                          (transⁿ (symⁿ (⊙-congʳ _ (⊙-congʳ _ (⊙-assoc _ _ _))))
                          (transⁿ (symⁿ (⊙-congʳ _ (⊙-congʳ _ (id-trans-unitˡ _))))
                          (transⁿ (symⁿ (⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (isoʳ (mod-cong μ (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))))))
                          (transⁿ (symⁿ (⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _))))))
                          (transⁿ (symⁿ (⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (mod-natural μ (Γ ⟪ f' ⟫ˡ)))))))))
                          (transⁿ (symⁿ (⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (⊙-congˡ _ (id-trans-unitʳ _))))))))
                          (transⁿ (symⁿ (⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))))))))))))
                          (transⁿ (symⁿ (⊙-assoc _ _ _))
                          (transⁿ (symⁿ (⊙-assoc _ _ _))
                          (transⁿ (symⁿ (⊙-congˡ _ (⊙-assoc _ _ _)))
                          (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))))
                          (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))))
                          (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)))))
                          (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)))))
                          (transⁿ (symⁿ (⊙-congʳ _ (mod-natural-⊚' μ _ _)))
                          (transⁿ (symⁿ (⊙-assoc _ _ _))
                          (transⁿ (symⁿ (⊙-congˡ _ (⊙-assoc _ _ _)))
                          (transⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)))
                          (transⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoˡ (mod-cong μ (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))))))
                          (transⁿ (⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _)))
                          (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _))
                          (transⁿ (⊙-congˡ _ (⊙-congʳ _ (isoˡ (mod-natural μ (Γ ⟪ f' ⟫ˡ)))))
                          (transⁿ (⊙-congˡ _ (id-trans-unitʳ _))
                          (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _))
                          (transⁿ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))))))
                          (⊙-congˡ _ (id-trans-unitʳ _))))))))))))))))))))))))))))))))
            {-
              begin
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ))
              ≅˘⟨ id-trans-unitˡ _ ⟩
                id-trans (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ ]) ⊙ from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ))
              ≅˘⟨ ⊙-congˡ _ (isoˡ (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ))
              ≅⟨ ⊙-assoc _ _ _ ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ (from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))
              ≅˘⟨ ⊙-congʳ _ (id-trans-unitˡ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ (id-trans ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ) ] ⟩ ⊙ (from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ))))
              ≅˘⟨ ⊙-congʳ _ (⊙-congˡ _ (isoˡ (mod-cong μ (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                (from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ))))
              ≅⟨ ⊙-congʳ _ (⊙-assoc _ _ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                (from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))))
              ≅˘⟨ ⊙-congʳ _ (⊙-congʳ _ (⊙-assoc _ _ _)) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ))))
              ≅˘⟨ ⊙-congʳ _ (⊙-congʳ _ (id-trans-unitˡ _)) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                (id-trans ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ⊚ lock-fmap μ (Γ ⟪ f' ⟫ˡ) ] ⟩ ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))))
              ≅˘⟨ ⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (isoʳ (mod-cong μ (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                ((mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))))
              ≅˘⟨ ⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _)))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                ((mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                id-trans ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] [ lock-fmap μ (Γ ⟪ f' ⟫ˡ) ] ⟩ ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))))
              ≅˘⟨ ⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (mod-natural μ (Γ ⟪ f' ⟫ˡ))))))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                ((mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))))
              ≅˘⟨ ⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (⊙-congˡ _ (id-trans-unitʳ _)))))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                ((mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                id-trans (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] ⟩ [ Γ ⟪ f' ⟫ˡ ]) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))))
              ≅˘⟨ ⊙-congʳ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))))))))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                ((mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))))
              ≅˘⟨ ⊙-assoc _ _ _ ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                ((mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ))))
              ≅˘⟨ ⊙-assoc _ _ _ ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))
              ≅˘⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)))) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))  ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)))
              ≅˘⟨ ⊙-congʳ _ (mod-natural-⊚' μ _ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))))
              ≅˘⟨ ⊙-assoc _ _ _ ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅˘⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙
                mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙
                (mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoˡ (mod-cong μ (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙
                id-trans ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] [ lock-fmap μ (Γ ⟪ f' ⟫ˡ) ] ⟩ ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _)) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (⊙-congʳ _ (isoˡ (mod-natural μ (Γ ⟪ f' ⟫ˡ)))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
                id-trans (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] ⟩ [ Γ ⟪ f' ⟫ˡ ]) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (id-trans-unitʳ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (⊙-congʳ _ (isoʳ (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))))) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                id-trans (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] ⟩ [ Γ ⟪ f' ⟫ˡ ]) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
              ≅⟨ ⊙-congˡ _ (id-trans-unitʳ _) ⟩
                to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))  ∎
              where open ≅ⁿ-Reasoning
            -}
            
          commutativity₃ : ty-subst-map (Γ ⟪ f' ⟫ˡ) (mod-cong' μ (η₂ (mor-to-↣ˡ T f)))
                             ≅ⁿ
                           to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ from (mod-natural μ (Γ ⟪ f' ⟫ˡ))
          commutativity₃ = symⁿ (transⁿ (⊙-assoc _ _ _)
                                (transⁿ (⊙-congʳ _ (mod-natural-ty-eq' μ _ _))
                                (transⁿ (symⁿ (⊙-assoc _ _ _))
                                (transⁿ (⊙-congˡ _ (isoˡ (mod-natural μ (Γ ⟪ f' ⟫ˡ))))
                                (id-trans-unitˡ _)))))

          commutativity₄ : from (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])) ⊙ 
                           η₂ (mor-to-↣ˡ T (f' ∙[ C ] f))
                             ≅ⁿ
                           to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])) ⊙ 
                           from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                           ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f)) ⊙ 
                           η₂ (mor-to-↣ˡ T f')
          eq commutativity₄ _ = trans (sym (ty-comp (T ᵗʸ⟨ c₁ ⟩ˡ)))
                               (trans (sym (ty-comp T))
                               (trans (ty-cong T (×-≡,≡→≡ [ f-eq , g-eq ]))
                               (trans (ty-comp T)
                               (trans (ty-comp T)
                               (trans (ty-comp T)
                               (ty-comp (T ᵗʸ⟨ c₁ ⟩ˡ)))))))
            where 
              f-eq : (f' ∙[ C ] f) ∙[ C ] (hom-id C) ≡ f' ∙[ C ] ((hom-id C) ∙[ C ] (f ∙[ C ] (hom-id C)))
              f-eq = trans (∙assoc C) (cong (category-composition C f') (sym (hom-idˡ C)))

              g-eq : (hom-id V) ∙[ V ] ((hom-id V) ∙[ V ] (hom-id V)) ≡ 
                      (hom-id V) ∙[ V ] ((hom-id V) ∙[ V ] ((hom-id V) ∙[ V ] ((hom-id V) ∙[ V ] (hom-id V))))
              g-eq = cong (category-composition V (hom-id V)) (trans (sym (hom-idˡ V)) (sym (hom-idˡ V)))

          commutativity₄' : mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                            mod-cong' μ (η₂ (mor-to-↣ˡ T (f' ∙[ C ] f)))
                              ≅ⁿ
                            mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                            mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                            mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙
                            mod-cong' μ (η₂ (mor-to-↣ˡ T f'))
          commutativity₄' = transⁿ (symⁿ (mod-cong-trans' μ))
                           (transⁿ (mod-cong-cong' μ commutativity₄)
                           (transⁿ (mod-cong-trans' μ)
                           (transⁿ (⊙-congˡ _ (mod-cong-trans' μ))
                                   (⊙-congˡ _ (⊙-congˡ _ (mod-cong-trans' μ))))))

          proof = transⁿ (⊙-congˡ _ commutativity₁)
                 (transⁿ (⊙-assoc _ _ _) 
                 (transⁿ (⊙-congʳ _ commutativity₄') 
                 (transⁿ (⊙-assoc _ _ _) 
                 (transⁿ (symⁿ (⊙-congʳ _ (⊙-assoc _ _ _))) 
                 (transⁿ (symⁿ (⊙-assoc _ _ _)) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congʳ _ (⊙-assoc _ _ _)))) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-assoc _ _ _))) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (⊙-assoc _ _ _))))) 
                 (transⁿ (symⁿ (⊙-congʳ _ (id-trans-unitˡ _))) 
                 (transⁿ (symⁿ (⊙-congʳ _ (⊙-congˡ _ (isoʳ (mod-natural μ (Γ ⟪ f' ⟫ˡ)))))) 
                 (transⁿ (⊙-congʳ _ (⊙-assoc _ _ _)) 
                 (transⁿ (symⁿ (⊙-assoc _ _ _)) 
                 (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _)) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _)))) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (mod-natural μ (Γ ⟪ f' ⟫ˡ))))))) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)))) 
                 (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _)) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congʳ _ (⊙-assoc _ _ _))))
                 (transⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _)))) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))))))) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)))) 
                 (transⁿ (⊙-congˡ _  (⊙-assoc _ _ _)) 
                 (transⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))) 
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ commutativity₂))))
                 (transⁿ (symⁿ (⊙-congˡ _ (⊙-congʳ _ (⊙-congʳ _ commutativity₃))))
                         (symⁿ (⊙-congˡ _ (⊙-congʳ _ (ty-subst-map-comp _ _ _))))))))))))))))))))))))))))))
            {-
              begin
                to (mod-natural μ (Γ ⟪ f' ∙[ C ] f ⟫ˡ)) ⊙ mod-cong' μ (η₂ (mor-to-↣ˡ T (f' ∙[ C ] f)))
              ≅⟨ ⊙-congˡ _ commutativity₁ ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ 
                  to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                    mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (η₂ (mor-to-↣ˡ T (f' ∙[ C ] f)))
              ≅⟨ ⊙-assoc _ _ _ ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ 
                  to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                    (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (⊚-comp-const-substˡ f f')) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (η₂ (mor-to-↣ˡ T (f' ∙[ C ] f))))
              ≅⟨ ⊙-congʳ _ commutativity₄' ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ 
                  to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙
                    (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅⟨ ⊙-assoc _ _ _ ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ 
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙
                    (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f'))))
              ≅˘⟨ ⊙-congʳ _ (⊙-assoc _ _ _)  ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ 
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙
                    (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f)))) ⊙
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-assoc _ _ _ ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                    (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙  
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))))) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f'))
              ≅˘⟨ ⊙-congˡ _ (⊙-congʳ _ (⊙-assoc _ _ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                    (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙  
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f)))) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f'))
              ≅˘⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                    (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))))) ⊙  
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f'))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (⊙-assoc _ _ _))) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                    mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙  
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f'))
              ≅˘⟨ ⊙-congʳ _ (id-trans-unitˡ _) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                    mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙  
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                          (id-trans _ ⊙ 
                            mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congʳ _ (⊙-congˡ _ (isoʳ (mod-natural μ (Γ ⟪ f' ⟫ˡ)))) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                    mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙  
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                          (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                            to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                              mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅⟨ ⊙-congʳ _ (⊙-assoc _ _ _) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙  
                    mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                      (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        mod-cong' μ (η₂ (mor-to-↣ˡ T f'))))
              ≅˘⟨ ⊙-assoc _ _ _ ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙  
                    mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                      from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙  
                    (mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                    from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                      (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                      mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙ 
                    id-trans _ ⊙ 
                        (mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (mod-natural μ (Γ ⟪ f' ⟫ˡ))))) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙ 
                    (from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙  
                    to (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                        (mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙  
                        to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        (mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙  
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        (mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congʳ _ (⊙-assoc _ _ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ))))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙  
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙  
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                    id-trans _ ⊙  
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoʳ (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))))) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                    (from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                      to (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙  
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                    from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                      ty-subst-map (Γ ⟪ f' ⟫ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙  
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                        from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                          (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅⟨ ⊙-congˡ _  (⊙-assoc _ _ _) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ))) ⊙ 
                    from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ 
                      (ty-subst-map (Γ ⟪ f' ⟫ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙  
                      (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                      mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                      from (mod-natural μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                        mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ Γ ⟪ f' ⟫ˡ)) ⊙ 
                  mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ 
                  mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) (lock-fmap μ (Γ ⟪ f ⟫ˡ)) (lock-fmap μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                  from (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                  from (ty-subst-cong-ty (Γ ⟪ f' ⟫ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙ 
                    (ty-subst-map (Γ ⟪ f' ⟫ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙  
                    (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                    mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                    from (mod-natural μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                      (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                      mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ commutativity₂))  ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) ⊙ 
                (ty-subst-map (Γ ⟪ f' ⟫ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙  
                (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f' ⟫ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ 
                from (mod-natural μ (Γ ⟪ f' ⟫ˡ)))) ⊙ 
                (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congʳ _ (⊙-congʳ _ commutativity₃)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) ⊙ 
                    (ty-subst-map (Γ ⟪ f' ⟫ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙  
                      ty-subst-map (Γ ⟪ f' ⟫ˡ) (mod-cong' μ (η₂ (mor-to-↣ˡ T f)))) ⊙ 
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f')))
              ≅˘⟨ ⊙-congˡ _ (⊙-congʳ _ (ty-subst-map-comp _ _ _)) ⟩
                to (ty-subst-cong-subst (⊚-comp-const-substˡ f f') ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙
                  from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (Γ ⟪ f' ⟫ˡ)) ⊙ 
                    (ty-subst-map (Γ ⟪ f' ⟫ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ 
                      mod-cong' μ (η₂ (mor-to-↣ˡ T f)))) ⊙ 
                        (to (mod-natural μ (Γ ⟪ f' ⟫ˡ)) ⊙ 
                          mod-cong' μ (η₂ (mor-to-↣ˡ T f'))) ∎
              where open ≅ⁿ-Reasoning
            -}

lift-ty : Ty (lift-ctx Γ) → Ty Γ
lift-ty T ⟨ [ c , w ] , γ ⟩ = lift-ty-obj T [ c , w ] γ
(lift-ty T) ⟪ [ f , g ] , eγ ⟫ t = lift-ty-mor T f g eγ t
ty-cong (lift-ty T) e-hom = lift-ty-cong T e-hom
ty-id (lift-ty T) = lift-ty-id T
ty-comp (lift-ty T) = lift-ty-comp T


--------------------------------------------------
-- Properties of ⟨ μ̃ ∣ _ ⟩

lift-mod-cong' : {Γ : Ctx C×W} {T S : Ty (lift-ctx Γ)} → T ↣ S → lift-ty T ↣ lift-ty S
func (lift-mod-cong' η) {[ c , w ]} {γ} = func (mod-cong' μ (ty-subst-map ⇆ (η ₙ⟨ c ⟩ˡ))) {w} {γ}
_↣_.naturality (lift-mod-cong' {Γ} {T} {S} η) {[ c₁ , w₁ ]} {[ c₂ , w₂ ]} {[ f , g ]} {γ₂} {γ₁} {eγ} {t} = proof
  where
    {-
                                              ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , _ ⟫_
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟨ w₁ , γ₁ ⟩ ←------------------------------------- ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩ ∋ s
                                      |                                                                          |
           func (lift-mod-cong' η) |                                                                          | func (lift-mod-cong' η)
                                      ↓                                                                          ↓
      ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟨ w₁ , γ₁ ⟩ ←------------------------------------- ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩
                                              ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , _ ⟫_
    -}
    commutativity₁ : {s : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩} → 
                     lift-ty-mor-W S g (eγ-decompnˡ Γ eγ) (func (lift-mod-cong' η) s) ≡ func (lift-mod-cong' η) (lift-ty-mor-W T g (eγ-decompnˡ Γ eγ) s)
    commutativity₁ = _↣_.naturality (mod-cong' μ (ty-subst-map ⇆ (η ₙ⟨ c₁ ⟩ˡ)))

    {-
                                                                  func (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))
            ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩ ←------------------------------------ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap (Γ ⟪ f ⟫ˡ) ] ⟩ ⟨ w₂ , γ₂ ⟩ ∋ s
                                                           |                                                                               |
      func (ty-subst-map (Γ ⟪ f ⟫ˡ) (lift-mod-cong' η)) |                    func (mod-cong' μ (ty-subst-map (lock-fmap (Γ ⟪ f ⟫ˡ)) φ₁)) | 
                                                           ↓                                                                               ↓
            ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] ⟨ w₂ , γ₂ ⟩ ←------------------------------------ ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap (Γ ⟪ f ⟫ˡ) ] ⟩ ⟨ w₂ , γ₂ ⟩
                                                                  func (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))                     
    -}
    φ₁ : T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ↣ S ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]
    φ₁ = ty-subst-map ⇆ (η ₙ⟨ c₁ ⟩ˡ)

    commutativity₂ : to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁) 
                       ≅ⁿ
                     ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ))

    commutativity₂ = transⁿ (symⁿ (id-trans-unitʳ _))
                    (transⁿ (symⁿ (⊙-congʳ (to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁)) (isoʳ (mod-natural μ (Γ ⟪ f ⟫ˡ)))))
                    (transⁿ (symⁿ (⊙-assoc (to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁)) (from (mod-natural μ (Γ ⟪ f ⟫ˡ))) (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))))
                    (transⁿ (⊙-congˡ (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (⊙-assoc (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁)) (from (mod-natural μ (Γ ⟪ f ⟫ˡ)))))
                    (transⁿ (⊙-congˡ (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (⊙-congʳ (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (mod-natural-ty-eq' μ (Γ ⟪ f ⟫ˡ) φ₁)))
                    (transⁿ (symⁿ (⊙-congˡ (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (⊙-assoc (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (from (mod-natural μ (Γ ⟪ f ⟫ˡ))) (ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁)))))
                    (transⁿ (⊙-assoc (to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ))) (ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁)) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))))
                    (transⁿ (⊙-congˡ (ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (isoˡ (mod-natural μ (Γ ⟪ f ⟫ˡ))))
                    (id-trans-unitˡ _))))))))
      {-
        begin
          to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁) 
        ≅˘⟨ id-trans-unitʳ _ ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁) ⊙ id-trans ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] ⟩
        ≅˘⟨ ⊙-congʳ (to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁)) (isoʳ (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁) ⊙ (from (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅˘⟨ ⊙-assoc (to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁)) (from (mod-natural μ (Γ ⟪ f ⟫ˡ))) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ))
        ≅⟨ ⊙-congˡ (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (⊙-assoc (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁)) (from (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ (mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ))
        ≅⟨ ⊙-congˡ (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (⊙-congʳ (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (mod-natural-ty-eq' μ (Γ ⟪ f ⟫ˡ) φ₁)) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ (from (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁)) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ))
        ≅˘⟨ ⊙-congˡ (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (⊙-assoc (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (from (mod-natural μ (Γ ⟪ f ⟫ˡ))) (ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ))
        ≅⟨ ⊙-assoc (to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ))) (ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁)) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ)) ⊙ (ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ (ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ))) (isoˡ (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⟩
          id-trans (⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ]) ⊙ (ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ id-trans-unitˡ _ ⟩
          ty-subst-map (Γ ⟪ f ⟫ˡ) (mod-cong' μ φ₁) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ)) ∎
        where open ≅ⁿ-Reasoning
      -}

    {-
                                                                        mod-cong' μ (η₂ (mor-to-↣ˡ T f))
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap (Γ ⟪ f ⟫ˡ ]) ⟩ ⟨ w₂ , γ₂ ⟩ ←--------------------------------- ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ⟩ ⟨ w₂ , γ₂ ⟩
                                                           |                                                      |
      mod-cong' μ (ty-subst-map (lock-fmap (Γ ⟪ f ⟫ˡ)) φ₁) |                                                      | mod-cong' μ φ₂
                                                           ↓                                                      ↓
      ⟨ μ ∣ S ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] [ lock-fmap (Γ ⟪ f ⟫ˡ ]) ⟩ ⟨ w₂ , γ₂ ⟩ ←--------------------------------- ⟨ μ ∣ S ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ⟩ ⟨ w₂ , γ₂ ⟩
                                                                        mod-cong' μ (η₂ (mor-to-↣ˡ S f))
    -}
    φ₂ : T ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ↣ S ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ]
    φ₂ = ty-subst-map ⇆ (η ₙ⟨ c₂ ⟩ˡ)

    commutativity₃ : η₂ (mor-to-↣ˡ S f) ⊙ φ₂ ≅ⁿ ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁ ⊙ η₂ (mor-to-↣ˡ T f)
    eq commutativity₃ {v} {γ} t = trans (sym (ty-comp S)) (trans (_↣_.naturality η) (cong (func η) (ty-comp T)))

    commutativity₃' : mod-cong' μ (η₂ (mor-to-↣ˡ S f)) ⊙ mod-cong' μ φ₂ ≅ⁿ mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁) ⊙ mod-cong' μ (η₂ (mor-to-↣ˡ T f))
    commutativity₃' = 
      begin
        mod-cong' μ (η₂ (mor-to-↣ˡ S f)) ⊙ mod-cong' μ φ₂
      ≅˘⟨ mod-cong-trans' μ ⟩
        mod-cong' μ (η₂ (mor-to-↣ˡ S f) ⊙ φ₂)
      ≅⟨ mod-cong-cong' μ commutativity₃ ⟩
        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁ ⊙ η₂ (mor-to-↣ˡ T f))
      ≅⟨ mod-cong-trans' μ ⟩
        mod-cong' μ (ty-subst-map (lock-fmap μ (Γ ⟪ f ⟫ˡ)) φ₁) ⊙ mod-cong' μ (η₂ (mor-to-↣ˡ T f)) ∎
      where open ≅ⁿ-Reasoning

    proof : lift-ty S ⟪ [ f , g ] , eγ ⟫ (func (lift-mod-cong' η) t) ≡ func (lift-mod-cong' η) (lift-ty T ⟪ [ f , g ] , eγ ⟫ t)
    proof = trans (cong (λ r → lift-ty-mor-W S g (eγ-decompnˡ Γ eγ) (func (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) r)) (eq commutativity₃' t))
           (trans (cong (lift-ty-mor-W S g (eγ-decompnˡ Γ eγ)) (eq commutativity₂ _))
                   commutativity₁)

lift-mod-cong-refl' : {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} → lift-mod-cong' (id-trans T) ≅ⁿ id-trans (lift-ty T)
eq lift-mod-cong-refl' t = eq (transⁿ (mod-cong-cong' μ (ty-subst-map-cong fix-ty-↣-idˡ)) (transⁿ (mod-cong-cong' μ (ty-subst-map-id ⇆)) (mod-cong-refl' μ))) t

lift-mod-cong-trans' : {Γ : Ctx C×W} {R T S : Ty (lift-ctx Γ)} {η : R ↣ T} {φ : T ↣ S} →
                      lift-mod-cong' (φ ⊙ η) ≅ⁿ lift-mod-cong' φ ⊙ lift-mod-cong' η
eq (lift-mod-cong-trans' {η = η} {φ = φ}) t = eq (transⁿ (mod-cong-cong' μ (ty-subst-map-cong fix-ty-↣-compˡ)) (transⁿ (mod-cong-cong' μ (ty-subst-map-comp ⇆ (φ ₙ⟨ _ ⟩ˡ) (η ₙ⟨ _ ⟩ˡ))) (mod-cong-trans' μ))) t

lift-mod-cong-cong' : {Γ : Ctx C×W} {T S : Ty (lift-ctx Γ)} {η η' : T ↣ S} → η ≅ⁿ η' → 
                      lift-mod-cong' η ≅ⁿ lift-mod-cong' η'
eq (lift-mod-cong-cong' η=η') t = eq (mod-cong-cong' μ (ty-subst-map-cong (fix-ty-↣-congˡ η=η'))) t 

lift-subst-naturalˡ : (σ : Δ ⇒ Γ) (T : Ty (lift-ctx Γ)) {c : Ob C} → 
                      (T [ lift-subst σ ]) ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ]
lift-subst-naturalˡ σ T {c} = transᵗʸ (ty-subst-cong-ty ⇆ fix-ty-subst-naturalˡ) lift-ctx-fix-subst-naturalˡ 
  {-
      func (from (lift-subst-naturalˡ σ T)) t 
    = func (from lift-ctx-fix-subst-naturalˡ ) 
        (func (from (ty-subst-cong-ty ⇆ fix-ty-subst-naturalˡ)) t)
    = ty-ctx-subst (T ᵗʸ⟨ c ⟩ˡ) refl 
      (func (from (ty-subst-cong-ty ⇆ fix-ty-subst-naturalˡ)) t)
    = ty-ctx-subst (T ᵗʸ⟨ c ⟩ˡ) refl t
      
      func (to (lift-subst-naturalˡ σ T)) t 
    = ty-ctx-subst (T ᵗʸ⟨ c ⟩ˡ) refl t
  -}

lift-mod-natural : {Δ Γ : Ctx C×W} (σ : Δ ⇒ Γ) {T : Ty (lift-ctx Γ)} →
                   (lift-ty T) [ σ ] ≅ᵗʸ lift-ty (T [ lift-subst σ ])
func (from (lift-mod-natural σ {T})) {[ c , _ ]} = func (from (transᵗʸ (mod-natural μ (σ ˢ⟨ c ⟩ˡ)) (symᵗʸ (mod-cong μ (lift-subst-naturalˡ σ T)))))
_↣_.naturality (from (lift-mod-natural {Δ} {Γ} σ {T})) {[ c₁ , _ ]} {[ c₂ , w₂ ]} {[ f , g ]} {γ₂} {eγ = eγ} {t} = proof
  where
    {- 
                                                              (lift-ty T) [ σ ] ⟪ [ f , g ] , eγ ⟫_
      ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ σ ˢ⟨ c₁ ⟩ˡ ] ⟨ w₁ , γ₁ ⟩ ←------------------------------------ ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ⟩ [ σ ˢ⟨ c₂ ⟩ˡ ] ⟨ w₂ , γ₂ ⟩ ∋ t
                          |                                                                                                         |
                          | func (T ↣ S)                                                                              func (T ↣ S) |
                          ↓                                                                                                         ↓
      ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟨ w₁ , γ₁ ⟩ ←---------------------------------------- ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₂ ⟩ˡ [ ⇆ ] ⟩ ⟨ w₂ , γ₂ ⟩
                                                                  lift-ty (T [ lift-subst σ ]) ⟪ f , eγ ⟫_
    -}
    commutativity₁ : to (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))) ⊙ from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))
                      ≅ⁿ 
                     ty-subst-map (σ ˢ⟨ c₂ ⟩ˡ) (mod-cong' μ (η₂ (mor-to-↣ˡ T f)))
    commutativity₁ = transⁿ (⊙-assoc _ _ _) 
                    (transⁿ (⊙-congʳ _ (mod-natural-ty-eq' μ _ _))
                    (transⁿ (symⁿ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congˡ _ (isoˡ (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))))
                            (id-trans-unitˡ _))))
    
    commutativity₂ : to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
                     mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
                     mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                     from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))
                       ≅ⁿ
                     from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ 
                     to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) 
    commutativity₂ = transⁿ (symⁿ (id-trans-unitʳ _))
                    (transⁿ (symⁿ (⊙-congʳ _ (isoʳ (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))))))
                    (transⁿ (symⁿ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _))
                    (transⁿ (symⁿ (⊙-congˡ _ (⊙-congʳ _ (⊙-assoc _ _ _))))
                    (transⁿ (⊙-congˡ _ (⊙-congʳ _ (mod-natural-⊚' μ _ _)))
                    (transⁿ (symⁿ (⊙-congˡ _ (⊙-assoc _ _ _)))
                    (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))))
                    (transⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))))
                    (transⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoˡ (mod-cong μ (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))))))
                    (transⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _))))
                    (transⁿ (⊙-congˡ _ (⊙-congˡ _ (isoˡ (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)))))
                    (⊙-congˡ _ (id-trans-unitˡ _))))))))))))))
      {-
        begin
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
          from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))
        ≅˘⟨ id-trans-unitʳ _ ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
          from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ 
          id-trans _ 
        ≅˘⟨ ⊙-congʳ _ (isoʳ (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
          from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ 
          (from (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))))
        ≅˘⟨ ⊙-assoc _ _ _ ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
          from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ 
          from (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
          (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ 
          from (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
          (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ 
          from (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))))) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅˘⟨ ⊙-congˡ _ (⊙-congʳ _ (⊙-assoc _ _ _)) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
          from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ 
          from (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ _ (⊙-congʳ _ (mod-natural-⊚' μ _ _)) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ))) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅˘⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))) ⊙
          from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _)) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-assoc _ _ _))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
          mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])))) ⊙
          from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congʳ _ (isoˡ (mod-cong μ (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          id-trans _ ⊙
          from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (id-trans-unitʳ _))) ⟩
          to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ _ (⊙-congˡ _ (isoˡ (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)))) ⟩
          id-trans _ ⊙ 
          from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) ⊙
          to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ)))
        ≅⟨ ⊙-congˡ _ (id-trans-unitˡ _) ⟩
          from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) ⊙ to (ty-subst-cong-ty (σ ˢ⟨ c₂ ⟩ˡ) (mod-natural μ (Γ ⟪ f ⟫ˡ))) ∎
        where open ≅ⁿ-Reasoning
      -}
    
    commutativity₃ : from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ 
                     to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))
                       ≅ⁿ
                     to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ 
                     mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])))
    commutativity₃ = transⁿ (symⁿ (⊙-congˡ _ (id-trans-unitˡ _)))
                    (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (isoˡ (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ))))))
                    (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congˡ _ (⊙-congʳ _ (mod-natural-subst-eq' μ _)))
                    (transⁿ (⊙-assoc _ _ _)
                    (transⁿ (⊙-congʳ _ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congʳ _ (⊙-congʳ _ (isoʳ (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)))))
                            (⊙-congʳ _ (id-trans-unitʳ _))))))))
      {-
        begin
          from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))
        ≅˘⟨ ⊙-congˡ _ (id-trans-unitˡ _) ⟩
          id-trans _ ⊙ from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))
        ≅˘⟨ ⊙-congˡ _ (⊙-congˡ _ (isoˡ (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)))) ⟩
          to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))
        ≅⟨ ⊙-congˡ _ (⊙-assoc _ _ _) ⟩
          to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩)) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))
        ≅⟨ ⊙-congˡ _ (⊙-congʳ _ (mod-natural-subst-eq' μ _)) ⟩
          to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))
        ≅⟨ ⊙-assoc _ _ _ ⟩
          to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)))
        ≅⟨ ⊙-congʳ _ (⊙-assoc _ _ _) ⟩
          to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ (from (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)) ⊙ to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ))))
        ≅⟨ ⊙-congʳ _ (⊙-congʳ _ (isoʳ (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)))) ⟩
          to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙ id-trans _)
        ≅⟨ ⊙-congʳ _ (id-trans-unitʳ _) ⟩
          to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)) ⊙ mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ∎
        where open ≅ⁿ-Reasoning
      -}
    commutativity₄ : to (mod-natural μ (Δ ⟪ f ⟫ˡ)) ⊙ 
                     mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙ 
                     mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) 
                       ≅ⁿ
                     from (ty-subst-cong-ty (Δ ⟪ f ⟫ˡ) (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))) ⊙
                     to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) ⊙
                     to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ))
    commutativity₄ = transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (id-trans-unitˡ _))))
                    (transⁿ (symⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (isoʳ (ty-subst-cong-ty (Δ ⟪ f ⟫ˡ) (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))))))))
                    (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congˡ _ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congˡ _ (⊙-congʳ _ (to-eq (mod-natural-⊚ μ _ _))))
                    (transⁿ (symⁿ (⊙-congˡ _ (⊙-assoc _ _ _)))
                    (transⁿ (⊙-assoc _ _ _)
                    (transⁿ (⊙-congʳ _ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congʳ _ (⊙-congʳ _ (isoˡ (mod-cong μ (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))))
                    (⊙-congʳ _ (id-trans-unitʳ _))))))))))

    commutativity₅ : to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _) ⊙
                     from (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])) ⊙
                     from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])) ⊙
                     to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ])) ⊙
                     from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _) ⊙
                     ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))
                       ≅ⁿ
                     ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (from (lift-subst-naturalˡ σ T)) ⊙
                     η₂ (mor-to-↣ˡ (T [ lift-subst σ ]) f) ⊙
                     to (lift-subst-naturalˡ σ T)
    eq commutativity₅ s = trans (sym (trans (ty-comp T)
                                     (trans (ty-comp (T ᵗʸ⟨ c₁ ⟩ˡ))
                                     (trans (ty-comp (T ᵗʸ⟨ c₁ ⟩ˡ))
                                            (ty-comp (T ᵗʸ⟨ c₁ ⟩ˡ))))))
                         (trans (ty-cong T (×-≡,≡→≡ [ sym (hom-idˡ C) , hom-idˡ V ]))
                         (trans (ty-comp T)
                         (trans (ty-comp T)
                                (ty-comp (T ᵗʸ⟨ c₁ ⟩ˡ)))))

    commutativity₅' : mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                      mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
                      mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
                      mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))) ⊙
                      mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)) ⊙
                      mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f)))
                        ≅ⁿ
                      mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (from (lift-subst-naturalˡ σ T))) ⊙ 
                      mod-cong' μ (η₂ (mor-to-↣ˡ (T [ lift-subst σ ]) f)) ⊙ 
                      mod-cong' μ (to (lift-subst-naturalˡ σ T))
    commutativity₅' = transⁿ (symⁿ (transⁿ (mod-cong-trans' μ)
                                   (transⁿ (⊙-congˡ _ (mod-cong-trans' μ))
                                   (transⁿ (⊙-congˡ _ (⊙-congˡ _ (mod-cong-trans' μ)))
                                   (transⁿ (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (mod-cong-trans' μ))))
                                           (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (⊙-congˡ _ (mod-cong-trans' μ))))))))))
                      (transⁿ (mod-cong-cong' μ commutativity₅)
                      (transⁿ (mod-cong-trans' μ)
                              (⊙-congˡ _ (mod-cong-trans' μ))))
 
    commutativity₆ : to (mod-natural μ (Δ ⟪ f ⟫ˡ)) ⊙
                     mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (to (lift-subst-naturalˡ σ T)))
                       ≅ⁿ
                     ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))) ⊙ 
                     to (mod-natural μ (Δ ⟪ f ⟫ˡ))   
    commutativity₆ = to-eq (mod-natural-ty-eq μ (Δ ⟪ f ⟫ˡ) (lift-subst-naturalˡ σ T))

    commutativity₇ : {s : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ [ Γ ⟪ f ⟫ˡ ] [ σ ˢ⟨ c₂ ⟩ˡ ] ⟨ w₂ , γ₂ ⟩} →
                      ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫ 
                        (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))
                          (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))) 
                            (func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)))
                              (func (from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩))
                                (func (from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ))) s)))))
                        ≡
                      func (mod-cong' μ (to (lift-subst-naturalˡ σ T)))
                        (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))) 
                          (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , eγ-decompnˡ Γ (ty-subst-new-proof σ eγ) ⟫ s))
    commutativity₇ = trans (_↣_.naturality (mod-cong' μ (to (lift-subst-naturalˡ σ T)))) 
                           (cong (func (mod-cong' μ (to (lift-subst-naturalˡ σ T)))) (trans (_↣_.naturality (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))))
                                 (trans (cong (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))) (sym (ty-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩)))
                                        (cong (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))) (ty-cong ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (hom-idˡ W))))))

    proof = trans (cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ))))) 
                        (sym (eq (isoˡ (mod-cong μ (ty-subst-cong-ty (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (lift-subst-naturalˡ σ T)))) _)))
            (trans (cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ)))) ∘ (func (mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (to (lift-subst-naturalˡ σ T)))))) 
                         (sym (eq commutativity₅' _)))
            (trans (cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ)))) ∘ (func (mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (to (lift-subst-naturalˡ σ T))))) ∘ (func (mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))) ∘ (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))) ∘ (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))) ∘ (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))) ∘ (func (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))))) 
                         (sym (eq (isoʳ (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) _)))
            (trans (cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_) 
                         (eq commutativity₆ _))
            (trans (cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T)))))) 
                         (eq commutativity₄ _))
            (trans (cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))) ∘ (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))) ∘ (func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ))))) 
                         (sym (eq commutativity₃ _)))
            (trans (cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))) ∘ (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))) ∘ (func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)))) ∘ (func (from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩)))) 
                   (eq commutativity₂ _))
            (trans commutativity₇
                  (cong (func (mod-cong' μ (to (lift-subst-naturalˡ σ T))) ∘ func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))) ∘ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , eγ-decompnˡ Γ (ty-subst-new-proof σ eγ) ⟫_ ∘ func (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))) 
                        (eq commutativity₁ t)))))))))
      {-
        begin
          ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫
            (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ))) 
              (func (mod-cong' μ (η₂ (mor-to-↣ˡ (T [ lift-subst σ ]) f)))
                (func (mod-cong' μ (to (lift-subst-naturalˡ σ T)))
                  (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t))))
        ≡⟨ cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ 
            (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ))))) (sym (eq (isoˡ (mod-cong μ (ty-subst-cong-ty (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (lift-subst-naturalˡ σ T)))) _)) ⟩
          ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫ 
            (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ)))
              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (to (lift-subst-naturalˡ σ T)))) 
                (func (mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (from (lift-subst-naturalˡ σ T))))
                  (func (mod-cong' μ (η₂ (mor-to-↣ˡ (T [ lift-subst σ ]) f)))
                    (func (mod-cong' μ (to (lift-subst-naturalˡ σ T)))
                      (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t))))))
        ≡⟨ cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ 
            (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ)))) ∘ 
              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (to (lift-subst-naturalˡ σ T)))))) (sym (eq commutativity₅' _)) ⟩
          ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫ 
            (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ)))
              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (to (lift-subst-naturalˡ σ T)))) 
                (func (mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))
                  (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                    (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                      (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                        (func (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))
                          (func (mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))))
                            (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t)))))))))
        ≡⟨ cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘
            (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ)))) ∘ 
              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (to (lift-subst-naturalˡ σ T))))) ∘ 
                (func (mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))) ∘ 
                  (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))) ∘ 
                    (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))) ∘ 
                      (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))) ∘ 
                        (func (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _))))) (sym (eq (isoʳ (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) _)) ⟩
          ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫ 
            (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ)))
              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (Δ ⟪ f ⟫ˡ)) (to (lift-subst-naturalˡ σ T)))) 
                (func (mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))
                  (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                    (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                      (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                        (func (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))
                          (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                            (func (to (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))))
                                (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t)))))))))))
        ≡⟨ cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_) (eq commutativity₆ _) ⟩
          ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫ 
            (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))
              (func (to (mod-natural μ (Δ ⟪ f ⟫ˡ))) 
                (func (mod-cong' μ (to (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))
                  (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-⊚ μ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                    (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                      (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                        (func (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))
                          (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                            (func (to (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))))
                                (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t)))))))))))
        ≡⟨ cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘ (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T)))))) (eq commutativity₄ _) ⟩
          ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫ 
            (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))
              (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))) 
                (func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)))
                  (func (to (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ ⊚ Δ ⟪ f ⟫ˡ)))
                    (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-const-substˡ σ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                      (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                        (func (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))
                          (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                            (func (to (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))))
                                (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t)))))))))))
        ≡⟨ cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘  
            (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))) ∘ 
              (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))) ∘  
                (func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ))))) (sym (eq commutativity₃ _)) ⟩
          ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫ 
            (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))
              (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))) 
                (func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)))
                  (func (from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩))
                    (func (to (mod-natural μ (Γ ⟪ f ⟫ˡ ⊚ σ ˢ⟨ c₂ ⟩ˡ)))
                      (func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-⊚ μ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ)) (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]))))
                        (func (mod-cong' μ (from (ty-subst-comp (T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ]) _ _)))
                          (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                            (func (to (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                              (func (mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))))
                                (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t)))))))))))
        ≡⟨ cong (⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫_ ∘  
            (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))) ∘ 
              (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))) ∘  
                (func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)))) ∘ 
                  (func (from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩)))) (eq commutativity₂ _) ⟩
          ⟨ μ ∣ (T [ lift-subst σ ]) ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , (eγ-decompnˡ Δ eγ) ⟫ 
            (func (ty-subst-map (Δ ⟪ f ⟫ˡ) (mod-cong' μ (to (lift-subst-naturalˡ σ T))))
              (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))) 
                (func (to (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (σ ˢ⟨ c₁ ⟩ˡ) (Δ ⟪ f ⟫ˡ)))
                  (func (from (ty-subst-cong-subst (fix-const-substˡ σ) ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩))
                    (func (from (ty-subst-comp ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ (Γ ⟪ f ⟫ˡ) (σ ˢ⟨ c₂ ⟩ˡ))) 
                      (func (ty-subst-map (σ ˢ⟨ c₂ ⟩ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))))
                        (func (to (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                          (func (mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))))
                            (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t)))) )))))      
        ≡⟨ commutativity₇ ⟩
          func (mod-cong' μ (to (lift-subst-naturalˡ σ T)))
            (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))
              (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , eγ-decompnˡ Γ (ty-subst-new-proof σ eγ) ⟫
                (func (ty-subst-map (σ ˢ⟨ c₂ ⟩ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))))
                  (func (to (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ)))
                    (func (mod-cong' μ (ty-subst-map (lock-fmap μ (σ ˢ⟨ c₂ ⟩ˡ)) (η₂ (mor-to-↣ˡ T f))))
                      (func (from (mod-natural μ (σ ˢ⟨ c₂ ⟩ˡ))) t))))))
        ≡⟨ cong (func (mod-cong' μ (to (lift-subst-naturalˡ σ T))) ∘ func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ))) ∘ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , eγ-decompnˡ Γ (ty-subst-new-proof σ eγ) ⟫_ ∘ func (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))) (eq commutativity₁ t) ⟩
          func (mod-cong' μ (to (lift-subst-naturalˡ σ T)))
            (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))
              (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , eγ-decompnˡ Γ (ty-subst-new-proof σ eγ) ⟫
                (func (ty-subst-map (σ ˢ⟨ c₂ ⟩ˡ) (to (mod-natural μ (Γ ⟪ f ⟫ˡ))))
                  (func (ty-subst-map (σ ˢ⟨ c₂ ⟩ˡ) (mod-cong' μ (η₂ (mor-to-↣ˡ T f)))) t))))
        ≡⟨⟩
          func (mod-cong' μ (to (lift-subst-naturalˡ σ T)))
            (func (from (mod-natural μ (σ ˢ⟨ c₁ ⟩ˡ)))
              (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇆ ] ⟩ ⟪ g , eγ-decompnˡ Γ (ty-subst-new-proof σ eγ) ⟫
                (func (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))
                  (func (mod-cong' μ (η₂ (mor-to-↣ˡ T f))) t)))) ∎
        where open ≡-Reasoning
      -}
func (to (lift-mod-natural σ {T})) {[ c , _ ]} {γ} = func (to (transᵗʸ (mod-natural μ (σ ˢ⟨ c ⟩ˡ)) (symᵗʸ (mod-cong μ (lift-subst-naturalˡ σ T)))))
-- TODO: ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ 
_↣_.naturality (to (lift-mod-natural σ {T})) {[ c₁ , w₁ ]} {[ c₂ , w₂ ]} {[ f , g ]} {γ₂} {γ₁} {eγ} {t} = {!   !}
eq (isoˡ (lift-mod-natural σ {T})) {[ c , _ ]} t = eq (isoˡ (transᵗʸ (mod-natural μ (σ ˢ⟨ c ⟩ˡ)) (symᵗʸ (mod-cong μ (lift-subst-naturalˡ σ T))))) t
eq (isoʳ (lift-mod-natural σ {T})) {[ c , _ ]} t = eq (isoʳ (transᵗʸ (mod-natural μ (σ ˢ⟨ c ⟩ˡ)) (symᵗʸ (mod-cong μ (lift-subst-naturalˡ σ T))))) t

lift-mod-natural-ty-eq' : {Δ Γ : Ctx C×W} (σ : Δ ⇒ Γ) {T S : Ty (lift-ctx Γ)} (η : T ↣ S) →
                          lift-mod-cong' (ty-subst-map (lift-subst σ) η) ⊙ from (lift-mod-natural σ {T = T})
                            ≅ⁿ
                          from (lift-mod-natural σ) ⊙ ty-subst-map σ (lift-mod-cong' η)
eq (lift-mod-natural-ty-eq' σ {S = S} η) t = trans (sym (eq (mod-cong-trans' μ) _))
                                            (trans (eq (mod-cong-cong' μ (record { eq = λ _ → sym (_↣_.naturality η) })) _)
                                            (trans (eq (mod-cong-trans' μ) _)
                                                   (cong (func (mod-cong' μ (to (lift-subst-naturalˡ σ S)))) (eq (mod-natural-ty-eq' μ _ _) _))))

lift-mod-natural-id' : {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} →
                        lift-mod-cong' (from (transᵗʸ (ty-subst-cong-subst lift-subst-id T) (ty-subst-id T))) ⊙ from (lift-mod-natural (id-subst Γ))
                          ≅ⁿ
                        from (ty-subst-id (lift-ty T))
eq (lift-mod-natural-id' {Γ} {T}) t = proof
  where
    commutativity₁ : {c : Ob C} → mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-cong μ (fix-subst-idˡ {Γ = Γ})) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ]))) ⊙
                                  from (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ))) ⊙
                                  from (ty-subst-cong-subst fix-subst-idˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩)
                                    ≅ⁿ
                                  from (mod-natural μ ((id-subst Γ) ˢ⟨ c ⟩ˡ))
    commutativity₁ = transⁿ (⊙-assoc _ _ _)
                    (transⁿ (⊙-congʳ _ (mod-natural-subst-eq' μ _))
                    (transⁿ (symⁿ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congˡ _ (isoˡ (mod-cong μ (ty-subst-cong-subst (lock-fmap-cong μ (fix-subst-idˡ {Γ = Γ})) (T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ])))))
                            (id-trans-unitˡ _))))

    commutativity₂ : {c : Ob C} → mod-cong' μ (to (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])))) ⊙ 
                                  from (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇆ ] ⟩)
                                    ≅ⁿ 
                                  from (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ)))
    commutativity₂ = transⁿ (symⁿ (⊙-congʳ _ (mod-natural-id' μ)))
                    (transⁿ (symⁿ (⊙-assoc _ _ _))
                    (transⁿ (⊙-congˡ _ (isoˡ (mod-cong μ (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ])) (ty-subst-id (T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ]))))))
                            (id-trans-unitˡ _) ))
    
    ↣-eq : {c : Ob C} → ty-subst-map ⇆ ((from (transᵗʸ (ty-subst-cong-subst lift-subst-id T) (ty-subst-id T))) ₙ⟨ c ⟩ˡ) ⊙ 
                        to (lift-subst-naturalˡ (id-subst Γ) T) ⊙
                        to (ty-subst-cong-subst (lock-fmap-cong μ (fix-subst-idˡ {Γ = Γ})) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])) ⊙ 
                        to (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])))
                          ≅ⁿ
                        id-trans (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])
    eq ↣-eq t = trans (sym (trans (ty-comp (T ᵗʸ⟨ _ ⟩ˡ)) (trans (ty-comp (T ᵗʸ⟨ _ ⟩ˡ)) (ty-comp (T ᵗʸ⟨ _ ⟩ˡ)))))
               (trans (ty-cong (T ᵗʸ⟨ _ ⟩ˡ) (trans (hom-idˡ V) (trans (hom-idˡ V) (hom-idˡ V)))) (ty-id (T ᵗʸ⟨ _ ⟩ˡ)))
    
    proof = trans (sym (trans (eq (mod-cong-trans' μ) _)
                       (trans (eq (mod-cong-trans' μ) _)
                       (trans (eq (mod-cong-trans' μ) _)
                       (trans (cong (func (mod-cong' μ (ty-subst-map ⇆ ((from (transᵗʸ (ty-subst-cong-subst lift-subst-id T) (ty-subst-id T))) ₙ⟨ _ ⟩ˡ))) ∘ func (mod-cong' μ (to (lift-subst-naturalˡ (id-subst Γ) T))) ∘ func (mod-cong' μ (to (ty-subst-cong-subst (lock-fmap-cong μ (fix-subst-idˡ {Γ = Γ})) (T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ]))))) (eq commutativity₂ _))
                              (cong (func (mod-cong' μ (ty-subst-map ⇆ ((from (transᵗʸ (ty-subst-cong-subst lift-subst-id T) (ty-subst-id T))) ₙ⟨ _ ⟩ˡ))) ∘ func (mod-cong' μ (to (lift-subst-naturalˡ (id-subst Γ) T)))) (eq commutativity₁ _)))))))
            (trans (eq (mod-cong-cong' μ ↣-eq) _)
            (trans (eq (mod-cong-refl' μ) _)
            (trans (ty-cong ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ] ⟩ refl)
                   (ty-id ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ] ⟩))))

lift-mod-natural-⊚' : {Δ Γ Θ : Ctx C×W} (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) {T : Ty (lift-ctx Θ)} →
                       lift-mod-cong' (from (ty-subst-comp T (lift-subst τ) (lift-subst σ))) ⊙ from (lift-mod-natural σ) ⊙ from (ty-subst-cong-ty σ (lift-mod-natural τ))
                         ≅ⁿ
                       lift-mod-cong' (from (ty-subst-cong-subst (lift-subst-⊚ τ σ) T)) ⊙ from (lift-mod-natural (τ ⊚ σ)) ⊙ from (ty-subst-comp (lift-ty T) τ σ)
eq (lift-mod-natural-⊚' {Δ} {Γ} {θ} τ σ {T}) t = 
  begin
    func (lift-mod-cong' (from (ty-subst-comp T (lift-subst τ) (lift-subst σ))))
      (func (from (lift-mod-natural σ))
        (func (from (ty-subst-cong-ty σ (lift-mod-natural τ))) t))
  ≡⟨ {!   !} ⟩
    func (lift-mod-cong' (from (ty-subst-cong-subst (lift-subst-⊚ τ σ) T)))
      (func (from (lift-mod-natural (τ ⊚ σ)))
        (func (from (ty-subst-comp (lift-ty T) τ σ)) t)) ∎
  where open ≡-Reasoning

lift-mod-natural-subst-eq' : {Δ Γ : Ctx C×W} {σ τ : Δ ⇒ Γ} {T : Ty (lift-ctx Γ)} (ε : σ ≅ˢ τ) →
                             from (lift-mod-natural τ) ⊙ from (ty-subst-cong-subst ε (lift-ty T))
                               ≅ⁿ
                             lift-mod-cong' (from (ty-subst-cong-subst (lift-subst-cong ε) T)) ⊙ from (lift-mod-natural σ)
eq (lift-mod-natural-subst-eq' {Δ} {Γ} {σ} {τ} {T} ε) t = proof
  where 
    -- commutativity₁ : ∀ {s} → lift-ty-mor T (hom-id C) (hom-id W) (trans (ctx-id Γ) (eq ε _)) s ≡ ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ] ⟩ (eq (fix-subst-congˡ ε) _) s
    -- commutativity₁ = {!   !}

    commutativity₂ : {c : Ob C} → to (lift-subst-naturalˡ τ T {c}) ⊙ from (ty-subst-cong-subst (lock-fmap-cong μ (fix-subst-congˡ ε)) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ]))
                                    ≅ⁿ
                                  ty-subst-map ⇆ ((from (ty-subst-cong-subst (lift-subst-cong ε) T)) ₙ⟨ c ⟩ˡ) ⊙ to (lift-subst-naturalˡ σ T)
    eq (commutativity₂ {c}) t = trans (sym (ty-comp (T ᵗʸ⟨ c ⟩ˡ))) (trans (ty-cong (T ᵗʸ⟨ c ⟩ˡ) refl) (ty-comp (T ᵗʸ⟨ c ⟩ˡ)))
    
    commutativity₂' : {c : Ob C} → mod-cong' μ (to (lift-subst-naturalˡ τ T {c})) ⊙ mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-subst-congˡ ε)) (T ᵗʸ⟨ c ⟩ˡ [ ⇆ ])))
                                     ≅ⁿ
                                   mod-cong' μ (ty-subst-map ⇆ ((from (ty-subst-cong-subst (lift-subst-cong ε) T)) ₙ⟨ c ⟩ˡ)) ⊙ mod-cong' μ (to (lift-subst-naturalˡ σ T))
    commutativity₂' = transⁿ (symⁿ (mod-cong-trans' μ)) (transⁿ (mod-cong-cong' μ commutativity₂) (mod-cong-trans' μ))

    proof = 
      begin
        func (mod-cong' μ (to (lift-subst-naturalˡ τ T)))
          (func (from (mod-natural μ (τ ˢ⟨ _ ⟩ˡ)))
            (lift-ty-mor T (hom-id C) (hom-id W) (trans (ctx-id Γ) (eq ε _)) t))
            -- (lift-ty-mor-W T (hom-id W) (eγ-decompnˡ Γ (trans (ctx-id Γ) (eq ε _))) (lift-ty-mor-C T (hom-id C) t)))
      ≡⟨ {!   !} ⟩
        func (mod-cong' μ (to (lift-subst-naturalˡ τ T)))
          (func (from (mod-natural μ (τ ˢ⟨ _ ⟩ˡ)))
            (ty-ctx-subst ⟨ μ ∣ T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ] ⟩ (eq (fix-subst-congˡ ε) _) t))
      ≡⟨ cong (func (mod-cong' μ (to (lift-subst-naturalˡ τ T)))) (eq (mod-natural-subst-eq' μ (fix-subst-congˡ ε)) t) ⟩
        func (mod-cong' μ (to (lift-subst-naturalˡ τ T)))
          (func (mod-cong' μ (from (ty-subst-cong-subst (lock-fmap-cong μ (fix-subst-congˡ ε)) (T ᵗʸ⟨ _ ⟩ˡ [ ⇆ ]))))
            (func (from (mod-natural μ (σ ˢ⟨ _ ⟩ˡ))) t))
      ≡⟨ eq commutativity₂' _ ⟩
        func (mod-cong' μ (ty-subst-map ⇆ ((from (ty-subst-cong-subst (lift-subst-cong ε) T)) ₙ⟨ _ ⟩ˡ)))
          (func (mod-cong' μ (to (lift-subst-naturalˡ σ T))) 
            (func (from (mod-natural μ (σ ˢ⟨ _ ⟩ˡ))) t)) ∎
      where open ≡-Reasoning