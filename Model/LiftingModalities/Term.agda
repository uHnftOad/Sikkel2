--------------------------------------------------
-- Lift an arbitrary modality μ between two modes V 
--  and W to a modality μ̃ : C×V → C×W
--------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Model.BaseCategory
open import Model.Modality

module Model.LiftingModalities.Term {C V W : BaseCategory} (μ : Modality V W) where

open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Product.Properties using (,-injective)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.LiftingModalities.Context {C} μ
open import Model.LiftingModalities.Type {C} μ

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
-- mod-intro μ̃

{-
  lift-ctx Γ ⊢ t : T
  lift-ctx Γ ⟨ c ⟩ˡ ⊢ t ᵗᵐ⟨ c ⟩ˡ : T ᵗʸ⟨ c ⟩ˡ
  Γ ⟨ c ⟩ˡ ,lock⟨ μ ⟩ ⊢ t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]' : T ᵗʸ⟨ c ⟩ˡ [ ⇋ ]
  Γ ⟨ c ⟩ˡ ⊢ mod-intro μ (t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]') : ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩
-} 
lift-tm : {T : Ty (lift-ctx Γ)} → Tm (lift-ctx Γ) T → Tm Γ (lift-ty T)
lift-tm t ⟨ [ c , w ] , γ ⟩' = mod-intro μ (t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]') ⟨ w , γ ⟩'
Tm.naturality (lift-tm {Γ} {T} t) {[ c₁ , w₁ ]} {[ c₂ , w₂ ]} {γ₂} {γ₁} [ f , g ] eγ = proof
  where
    open ≡-Reasoning
    helper : convert-term (➡₂ (mor-to-↣ˡ T f)) (t ᵗᵐ⟨ c₂ ⟩ˡ [ ⇋ ]') ≅ᵗᵐ t ᵗᵐ⟨ c₁ ⟩ˡ [ ⇋ ]' [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ]'
    eq helper δ =
      begin
        T ᵗʸ⟨ c₁ ⟩ˡ ⟪ hom-id V , _ ⟫
          T ᵗʸ⟨ _ ⟩ʳ ⟪ f , refl ⟫
            (t ⟨ [ c₂ , _ ] , _ ⟩')
      ≡⟨ sym (ty-comp T) ⟩
        T ⟪ [ f ∙[ C ] hom-id C , hom-id V ∙[ V ] hom-id V ] , _ ⟫
            (t ⟨ [ c₂ , _ ] , func ⇋ δ ⟩')
      ≡⟨ ty-cong T (×-≡,≡→≡ [ hom-idʳ C , hom-idˡ V ]) ⟩
        T ⟪ [ f , hom-id V ] , _ ⟫
            (t ⟨ [ c₂ , _ ] , func ⇋ δ ⟩')
      ≡⟨ Tm.naturality t [ f , hom-id V ] (eq lift-ctx-const-subst-natural-helperˡ δ) ⟩
        t ⟨ [ c₁ , _ ] , func ⇋ (func (lock-fmap μ (Γ ⟪ f ⟫ˡ)) δ) ⟩' ∎

    proof =
      begin
        ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫
          (func (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))
            (func (mod-hom μ (➡₂ (mor-to-↣ˡ T f)))
              (mod-intro μ (t ᵗᵐ⟨ c₂ ⟩ˡ [ ⇋ ]') ⟨ w₂ , γ₂ ⟩')))
      ≡⟨ cong (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫_ ∘ func (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))) (eq (mod-intro-convert μ (t ᵗᵐ⟨ c₂ ⟩ˡ [ ⇋ ]')) _) ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫
          func (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) 
            (mod-intro μ (convert-term (➡₂ (mor-to-↣ˡ T f)) (t ᵗᵐ⟨ c₂ ⟩ˡ [ ⇋ ]')) ⟨ w₂ , γ₂ ⟩')
      ≡⟨ cong (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫_ ∘ func (to (mod-natural μ (Γ ⟪ f ⟫ˡ)))) (eq (mod-intro-cong μ helper) _) ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫
          func (to (mod-natural μ (Γ ⟪ f ⟫ˡ))) 
            (mod-intro μ (t ᵗᵐ⟨ c₁ ⟩ˡ [ ⇋ ]' [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ]') ⟨ w₂ , γ₂ ⟩')
      ≡⟨ cong (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫_) (eq (symᵗᵐ (ι-convert-term {T=S = mod-natural μ (Γ ⟪ f ⟫ˡ)} {mod-intro μ (t ᵗᵐ⟨ c₁ ⟩ˡ [ ⇋ ]' [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ]')})) γ₂) ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫
          ι[ mod-natural μ (Γ ⟪ f ⟫ˡ) ] mod-intro μ (t ᵗᵐ⟨ c₁ ⟩ˡ [ ⇋ ]' [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ]') ⟨ w₂ , γ₂ ⟩'
      ≡⟨ cong (⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫_) (eq (symᵗᵐ (mod-intro-natural μ (Γ ⟪ f ⟫ˡ) (t ᵗᵐ⟨ c₁ ⟩ˡ [ ⇋ ]'))) _) ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫
          mod-intro μ (t ᵗᵐ⟨ c₁ ⟩ˡ [ ⇋ ]') [ Γ ⟪ f ⟫ˡ ]' ⟨ w₂ , γ₂ ⟩'
      ≡⟨ Tm.naturality (mod-intro μ (t ᵗᵐ⟨ c₁ ⟩ˡ [ ⇋ ]')) g (decompnˡ Γ eγ) ⟩
        mod-intro μ (t ᵗᵐ⟨ c₁ ⟩ˡ [ ⇋ ]') ⟨ w₁ , γ₁ ⟩' ∎

lift-mod-intro-cong : {T : Ty (lift-ctx Γ)} {t t' : Tm (lift-ctx Γ) T} →
                      t ≅ᵗᵐ t' → lift-tm t ≅ᵗᵐ lift-tm t'
eq (lift-mod-intro-cong t=t') _ = eq (mod-intro-cong μ (tm-subst-cong-tm ⇋ ((fix-tm-tm-congˡ t=t')))) _

lift-mod-intro-natural : (σ : Δ ⇒ Γ) {T : Ty (lift-ctx Γ)} (t : Tm (lift-ctx Γ) T) →
                         (lift-tm t) [ σ ]' ≅ᵗᵐ ι[ lift-mod-natural σ ] lift-tm (t [ lift-subst σ ]')
eq (lift-mod-intro-natural σ {T} t) {[ c , w ]} γ = proof
  where 
    helper : t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]' [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ]' 
               ≅ᵗᵐ
             convert-term (from (lift-subst-naturalˡ σ T)) ((t [ lift-subst σ ]') ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]')
    eq helper _ = sym (Tm.naturality t [ hom-id C , hom-id V ] (trans (ctx-id (lift-ctx _)) refl))

    open ≡-Reasoning
    proof = 
      begin 
        mod-intro μ (t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]') [ σ ˢ⟨ c ⟩ˡ ]' ⟨ w , γ ⟩'
      ≡⟨ eq (mod-intro-natural μ (σ ˢ⟨ c ⟩ˡ) (t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]')) γ ⟩
        func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ)))
          (mod-intro μ (t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]' [ lock-fmap μ (σ ˢ⟨ c ⟩ˡ) ]') ⟨ w , γ ⟩')
      ≡⟨ cong (func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ)))) (eq (mod-intro-cong μ helper) _) ⟩
        func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ)))
          (mod-intro μ (convert-term (from (lift-subst-naturalˡ σ T)) ((t [ lift-subst σ ]') ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]')) ⟨ w , γ ⟩')
      ≡⟨ cong (func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ)))) (sym (eq (mod-intro-convert μ _) γ)) ⟩
        func (to (mod-natural μ (σ ˢ⟨ c ⟩ˡ) {T ᵗʸ⟨ c ⟩ˡ [ ⇋ ]}))
          (convert-term (mod-hom μ (from (lift-subst-naturalˡ σ T)))
            (mod-intro μ ((t [ lift-subst σ ]') ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]')) ⟨ w , γ ⟩') ∎

lift-mod-intro-convert : {T S : Ty (lift-ctx Γ)} {η : T ↣ S} (t : Tm (lift-ctx Γ) T) →
                         convert-term (lift-mod-hom η) (lift-tm t) ≅ᵗᵐ lift-tm (convert-term η t)
eq (lift-mod-intro-convert _) _ = trans (eq (mod-intro-convert μ _) _) (eq (mod-intro-cong μ (record { eq = λ _ → refl})) _)

lift-ty-naturalˡ : {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} {c : Ob C} → 
                   (lift-ty T) ᵗʸ⟨ c ⟩ˡ ≅ᵗʸ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩
func (from lift-ty-naturalˡ) = id
_↣_.naturality (from (lift-ty-naturalˡ {Γ} {T} {c})) {f = g} {eγ = eγ} {t} = proof 
  where
    commutativity₁ : to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩) ⊙
                     to (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ))) ⊙ 
                     mod-hom μ (from (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])))
                       ≅ⁿ
                     to (mod-natural μ (Γ ⟪ hom-id C ⟫ˡ))
    commutativity₁ = transⁿ (⊙-congˡ _ (to-eq (mod-natural-subst-eq μ ≅ˢ-id-const-substˡ)))
                    (transⁿ (⊙-assoc _ _ _)
                    (transⁿ (⊙-congʳ _ (symⁿ (mod-hom-trans μ)))
                    (transⁿ (⊙-congʳ _ (mod-hom-cong μ (isoˡ (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])))))
                    (transⁿ (⊙-congʳ _ (mod-hom-refl μ))
                            (id-trans-unitʳ _)))))

    commutativity₂ : to (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩) ⊙
                     mod-hom μ (from (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ]))))
                       ≅ⁿ
                     to (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ)))
    commutativity₂ = transⁿ (⊙-congˡ _ (symⁿ (to-eq (mod-natural-id μ))))
                    (transⁿ (⊙-assoc _ _ _)
                    (transⁿ (⊙-congʳ _ (symⁿ (mod-hom-trans μ)))
                    (transⁿ (⊙-congʳ _ (mod-hom-cong μ (isoˡ (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ]))))))
                    (transⁿ (⊙-congʳ _ (mod-hom-refl μ))
                            (id-trans-unitʳ _)))))
    
    commutativity₃ : from (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ]))) ⊙ 
                     from (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])) ⊙ 
                     ➡₂ (mor-to-↣ˡ T (hom-id C))
                       ≅ⁿ
                     id-trans (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])
    eq commutativity₃ {v} δ = trans (sym (trans (ty-comp (T ᵗʸ⟨ c ⟩ˡ)) (ty-comp (T ᵗʸ⟨ c ⟩ˡ)))) (trans (sym (ty-comp T)) (trans (ty-cong T (×-≡,≡→≡ [ hom-idˡ C , trans (hom-idˡ V) (trans (hom-idˡ V) (hom-idˡ V)) ])) (ty-id T)))
    
    commutativity₃' : mod-hom μ (from (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])))) ⊙ 
                      mod-hom μ (from (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ]))) ⊙ 
                      mod-hom μ (➡₂ (mor-to-↣ˡ T (hom-id C)))
                        ≅ⁿ
                      id-trans ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩
    commutativity₃' = transⁿ (⊙-congˡ _ (symⁿ (mod-hom-trans μ))) (transⁿ (symⁿ (mod-hom-trans μ)) (transⁿ (mod-hom-cong μ commutativity₃) (mod-hom-refl μ)))

    open ≡-Reasoning
    proof = 
      begin
        ⟨ μ ∣ (T ᵗʸ⟨ c ⟩ˡ) [ ⇋ ] ⟩ ⟪ g , eγ ⟫ t
      ≡⟨ ty-cong ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ (sym (hom-idˡ W)) ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ hom-id W ∙[ W ] g , _ ⟫ t
      ≡⟨ ty-comp ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫ 
          ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ hom-id W , _ ⟫ t
      ≡⟨ cong (⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫_ ∘ func (to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩)) ∘ func (to (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩))) (sym (eq commutativity₃' _)) ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫ 
          func (to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩))
            (func (to (ty-subst-id ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩))
              (func (mod-hom μ (from (transᵗʸ (ty-subst-cong-subst (lock-fmap-id μ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])) (ty-subst-id (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ])))))
                (func (mod-hom μ (from (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ]))))
                  (func (mod-hom μ (➡₂ (mor-to-↣ˡ T (hom-id C)))) t))))
      ≡⟨ cong (⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫_ ∘ func (to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩))) (eq commutativity₂ _) ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫ 
          func (to (ty-subst-cong-subst ≅ˢ-id-const-substˡ ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩))
            (func (to (mod-natural μ (id-subst (Γ ⟨ c ⟩ˡ))))
              (func (mod-hom μ (from (ty-subst-cong-subst (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (T ᵗʸ⟨ c ⟩ˡ [ ⇋ ]))))
                (func (mod-hom μ (➡₂ (mor-to-↣ˡ T (hom-id C)))) t)))
      ≡⟨ cong (⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫_) (eq commutativity₁ _) ⟩
        ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩ ⟪ g , decompnˡ Γ eγ ⟫ 
          func (to (mod-natural μ (Γ ⟪ hom-id C ⟫ˡ)))
            (func (mod-hom μ (➡₂ (mor-to-↣ˡ T (hom-id C)))) t) ∎
func (to lift-ty-naturalˡ) = id
_↣_.naturality (to lift-ty-naturalˡ) = sym (_↣_.naturality (from lift-ty-naturalˡ)) 
eq (isoˡ lift-ty-naturalˡ) _ = refl
eq (isoʳ lift-ty-naturalˡ) _ = refl

-- lift-ty-natural-↣ˡ : {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} {c₁ c₂ : Ob C} {f : Hom C c₁ c₂} → 
--                      mor-to-↣ˡ (lift-ty T) f : (lift-ty T) ᵗʸ⟨ c₂ ⟩ˡ ↣ (lift-ty T) ᵗʸ⟨ c₁ ⟩ˡ [ Γ ⟪ f ⟫ˡ ]
--                      to lift-ty-naturalˡ {c = c₂} : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ ⇋ ] ⟩ ↣ (lift-ty T) ᵗʸ⟨ c₂ ⟩ˡ
--                       ≡
--                      ? : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ⟪ f ⟫ˡ ] [ ⇋ ] ⟩ ↣ ⟨ μ ∣ T [ ? ] ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩
--                      ? : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] ⟩ ↣ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ⟪ f ⟫ˡ ] [ ⇋ ] ⟩
--                      ? : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ ⇋ ] ⟩ ↣ ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ] ⟩

lift-tm-naturalˡ : {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} {t : Tm (lift-ctx Γ) T} {c : Ob C} → 
                   ι⁻¹[ lift-ty-naturalˡ ] ((lift-tm t) ᵗᵐ⟨ c ⟩ˡ) ≅ᵗᵐ mod-intro μ (t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]')
eq lift-tm-naturalˡ _ = refl

{-
  Γ ⟨ c₁ ⟩ˡ ⊢ ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c₁ ⟩ˡ) : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩
  Γ ⟨ c₂ ⟩ˡ ⊢ ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c₂ ⟩ˡ) : ⟨ μ ∣ T ᵗʸ⟨ c₂ ⟩ˡ [ ⇋ ] ⟩
  --------------------------------------------------
  Γ ⟨ c₂ ⟩ˡ ⊢ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c₁ ⟩ˡ)) [ Γ ⟪ f ⟫ˡ ]' : ⟨ μ ∣ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] ⟩ [ Γ ⟪ f ⟫ˡ ]


  T ᵗʸ⟨ c₁ ⟩ˡ [ lift-ctx Γ ⟪ f ⟫ˡ ] [ ⇋ ] ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ ⇋ ] [ lock-fmap μ (Γ ⟪ f ⟫ˡ) ]

  Γ ⊢ t : ⟨ μ̃ ∣ T ⟩ @ C×W
  --------------------------------------------------
  Γ ⟨ c ⟩ˡ ⊢ t ᵗᵐ⟨ c ⟩ˡ : ⟨ μ̃ ∣ T ⟩ ᵗʸ⟨ c ⟩ˡ @ W
  --------------------------------------------------
  Γ ⟨ c ⟩ˡ ⊢ (t ᵗᵐ⟨ c₂ ⟩ˡ) [ Γ ⟪ hom-id C ⟫ˡ ]' : ⟨ μ̃ ∣ T ⟩ ᵗʸ⟨ c ⟩ˡ [ Γ ⟪ hom-id C ⟫ˡ ]'
  --------------------------------------------------
  Γ ⟨ c ⟩ˡ ⊢ ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c ⟩ˡ) : ⟨ μ ∣ T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] ⟩
  --------------------------------------------------
  Γ ⟨ c ⟩ˡ ,lock ⟨ μ ⟩ ⊢ mod-elim μ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c ⟩ˡ)) : T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] @ V
  --------------------------------------------------
  lift-ctx Γ ⟨ c ⟩ˡ ⊢ mod-elim μ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c ⟩ˡ)) [ ⇋⁻¹ ]' : T ᵗʸ⟨ c ⟩ˡ [ ⇋ ] [ ⇋⁻¹ ]
-} 
lift-tm⁻¹ : {T : Ty (lift-ctx Γ)} → Tm Γ (lift-ty T) → Tm (lift-ctx Γ) T
lift-tm⁻¹ {T = T} t ⟨ [ c , v ] , γ ⟩' = mod-elim μ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c ⟩ˡ)) [ ⇋⁻¹ ]' ⟨ v , γ ⟩'
Tm.naturality (lift-tm⁻¹ {Γ} {T} t) {[ c₁ , v₁ ]} {[ c₂ , v₂ ]} {γ₂} {γ₁} [ f , g ] eγ =
  begin
    T ⟪ [ f , g ] , eγ ⟫ 
      mod-elim μ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c₂ ⟩ˡ)) ⟨ v₂ , γ₂ ⟩'
  ≡⟨ ty-cong T (sym (×-≡,≡→≡ [ hom-idˡ C , hom-idʳ V ])) ⟩
    T ⟪ [ hom-id C ∙[ C ] f , g ∙[ V ] hom-id V ] , _ ⟫
      (mod-elim μ (ι⁻¹[ lift-ty-naturalˡ {c = c₂} ] (t ᵗᵐ⟨ c₂ ⟩ˡ)) ⟨ v₂ , γ₂ ⟩')
  ≡⟨ ty-comp T ⟩
    T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫
      T ᵗʸ⟨ c₂ ⟩ˡ ⟪ g , refl ⟫
        (mod-elim μ (ι⁻¹[ lift-ty-naturalˡ {c = c₂} ] (t ᵗᵐ⟨ c₂ ⟩ˡ)) ⟨ v₂ , γ₂ ⟩')
  ≡⟨ cong (T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫_) (ty-cong (T ᵗʸ⟨ c₂ ⟩ˡ) refl) ⟩
    T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫
      T ᵗʸ⟨ c₂ ⟩ˡ ⟪ g , _ ⟫
        (mod-elim μ (ι⁻¹[ lift-ty-naturalˡ {c = c₂} ] (t ᵗᵐ⟨ c₂ ⟩ˡ)) ⟨ v₂ , γ₂ ⟩')
  ≡⟨ cong (T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫_) (Tm.naturality (mod-elim μ (ι⁻¹[ lift-ty-naturalˡ {c = c₂} ] (t ᵗᵐ⟨ c₂ ⟩ˡ))) g (cong (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩ ⟪ g ⟫_) (sym (eq (transˢ (lock-fmap-cong μ ≅ˢ-id-const-substˡ) (lock-fmap-id μ)) γ₂)))) ⟩
    T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫
      mod-elim μ (ι⁻¹[ lift-ty-naturalˡ {c = c₂} ] (t ᵗᵐ⟨ c₂ ⟩ˡ)) ⟨ v₁ , (lift-ctx Γ) ⟪ [ hom-id C {c₂} , g ] ⟫ γ₂ ⟩'
  ≡⟨ cong (T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫_) (sym {!   !}) ⟩ 
  -- (Tm.naturality (mod-elim μ (ι⁻¹[ lift-ty-naturalˡ {c = c₂} ] (t ᵗᵐ⟨ c₂ ⟩ˡ))) (hom-id V) (trans (ctx-id (lift-ctx Γ ⟨ c₂ ⟩ˡ)) (sym (_⇒_.naturality (lock-fmap μ (Γ ⟪ hom-id C ⟫ˡ))))))
    T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫
      T ᵗʸ⟨ c₂ ⟩ˡ ⟪ hom-id V , trans (ctx-id (lift-ctx Γ ⟨ c₂ ⟩ˡ)) (sym (_⇒_.naturality (lock-fmap μ (Γ ⟪ hom-id C ⟫ˡ)))) ⟫
        mod-elim μ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c₂ ⟩ˡ)) [ lock-fmap μ (Γ ⟪ hom-id C ⟫ˡ) ]' ⟨ v₁ , (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ γ₂ ⟩'
  ≡⟨ {!   !} ⟩ -- mod-elim-natural
    T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫
      T ᵗʸ⟨ c₂ ⟩ˡ ⟪ hom-id V , trans (ctx-id (lift-ctx Γ ⟨ c₂ ⟩ˡ)) (sym (_⇒_.naturality (lock-fmap μ (Γ ⟪ hom-id C ⟫ˡ)))) ⟫
        mod-elim μ (ι⁻¹[ mod-natural μ (Γ ⟪ hom-id C ⟫ˡ) ] ((ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c₂ ⟩ˡ)) [ Γ ⟪ hom-id C ⟫ˡ ]')) ⟨ v₁ , (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ γ₂ ⟩'
  ≡⟨ {!   !} ⟩ -- ι⁻¹-subst-commute
    T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫
      T ᵗʸ⟨ c₂ ⟩ˡ ⟪ hom-id V , trans (ctx-id (lift-ctx Γ ⟨ c₂ ⟩ˡ)) (sym (_⇒_.naturality (lock-fmap μ (Γ ⟪ hom-id C ⟫ˡ)))) ⟫
        mod-elim μ (ι⁻¹[ mod-natural μ (Γ ⟪ hom-id C ⟫ˡ) ] (ι⁻¹[ ty-subst-cong-ty (Γ ⟪ hom-id C ⟫ˡ) lift-ty-naturalˡ ] ((t ᵗᵐ⟨ c₂ ⟩ˡ) [ Γ ⟪ hom-id C ⟫ˡ ]'))) ⟨ v₁ , (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ γ₂ ⟩'
  ≡⟨ {!   !} ⟩
    T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫
      T ᵗʸ⟨ c₂ ⟩ˡ ⟪ hom-id V , trans (ctx-id (lift-ctx Γ ⟨ c₂ ⟩ˡ)) (sym (_⇒_.naturality (lock-fmap μ (Γ ⟪ hom-id C ⟫ˡ)))) ⟫
        mod-elim μ (ι⁻¹[ mod-natural μ (Γ ⟪ hom-id C ⟫ˡ) ] 
                   (ι⁻¹[ ty-subst-cong-ty (Γ ⟪ hom-id C ⟫ˡ) lift-ty-naturalˡ ] 
                   (ι[ ty-subst-cong-subst ≅ˢ-id-const-substˡ (lift-ty T ᵗʸ⟨ c₂ ⟩ˡ) ] (t ᵗᵐ⟨ c₂ ⟩ˡ [ id-subst _ ]')))) ⟨ v₁ , (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ γ₂ ⟩'
  ≡⟨ {!   !} ⟩
    T ᵗʸ⟨ v₁ ⟩ʳ ⟪ f , decompnʳ (lift-ctx Γ) eγ ⟫
      T ᵗʸ⟨ c₂ ⟩ˡ ⟪ hom-id V , trans (ctx-id (lift-ctx Γ ⟨ c₂ ⟩ˡ)) (sym (_⇒_.naturality (lock-fmap μ (Γ ⟪ hom-id C ⟫ˡ)))) ⟫
        mod-elim μ (ι⁻¹[ mod-natural μ (Γ ⟪ hom-id C ⟫ˡ) ] 
                   (ι⁻¹[ ty-subst-cong-ty (Γ ⟪ hom-id C ⟫ˡ) lift-ty-naturalˡ ] 
                   (ι[ ty-subst-cong-subst ≅ˢ-id-const-substˡ (lift-ty T ᵗʸ⟨ c₂ ⟩ˡ) ] 
                   (ι[ ty-subst-id (lift-ty T ᵗʸ⟨ c₂ ⟩ˡ) ] 
                      (t ᵗᵐ⟨ c₂ ⟩ˡ))))) ⟨ v₁ , (Γ ⟨ c₂ ⟩ˡ ,lock⟨ μ ⟩) ⟪ g ⟫ γ₂ ⟩'
  ≡⟨ {!   !} ⟩
    mod-elim μ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c₁ ⟩ˡ)) ⟨ v₁ , γ₁ ⟩' ∎
  where open ≡-Reasoning

lift-tm⁻¹-cong : {T : Ty (lift-ctx Γ)} {t t' : Tm Γ (lift-ty T)} →
                 t ≅ᵗᵐ t' → lift-tm⁻¹ t ≅ᵗᵐ lift-tm⁻¹ t'
eq (lift-tm⁻¹-cong t=t') γ = eq (mod-elim-cong μ (ι⁻¹-cong (fix-tm-tm-congˡ t=t'))) γ

lift-tm⁻¹-naturalˡ : {Γ : Ctx C×W} {T : Ty (lift-ctx Γ)} {t : Tm Γ (lift-ty T)} {c : Ob C} →
                     (lift-tm⁻¹ t) ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]' ≅ᵗᵐ mod-elim μ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c ⟩ˡ))
eq lift-tm⁻¹-naturalˡ γ = refl

lift-mod-β : {T : Ty (lift-ctx Γ)} (t : Tm (lift-ctx Γ) T) →
             lift-tm⁻¹ (lift-tm t) ≅ᵗᵐ t
eq (lift-mod-β t) {[ c , _ ]} γ = eq (transᵗᵐ (mod-elim-cong μ lift-tm-naturalˡ) (mod-β μ (t ᵗᵐ⟨ c ⟩ˡ [ ⇋ ]'))) γ

lift-mod-η : {T : Ty (lift-ctx Γ)} (t : Tm Γ (lift-ty T)) →
             lift-tm (lift-tm⁻¹ t) ≅ᵗᵐ t
eq (lift-mod-η t) {[ c , _ ]} γ = eq (transᵗᵐ (mod-intro-cong μ lift-tm⁻¹-naturalˡ) (mod-η μ (ι⁻¹[ lift-ty-naturalˡ ] (t ᵗᵐ⟨ c ⟩ˡ)))) γ
