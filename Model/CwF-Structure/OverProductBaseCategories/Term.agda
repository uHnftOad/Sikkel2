--------------------------------------------------
-- Types in contexts over product base categories
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.OverProductBaseCategories.Term {C D : BaseCategory} where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Data.Product renaming (_,_ to [_,_])
open import Function using (id; _∘_)

open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term
open import Model.CwF-Structure.OverProductBaseCategories.Context
open import Model.CwF-Structure.OverProductBaseCategories.Type

open BaseCategory

private
  C×D : BaseCategory
  C×D = C ⊗ D
  
  variable
    c c₁ c₂ c₃ : Ob C
    d d₁ d₂ d₃ : Ob D
    Γ Δ Θ : Ctx C×D

infixl 30 _ᵗᵐ⟨_⟩ˡ _ᵗᵐ⟨_⟩ʳ


--------------------------------------------------

fix-tmˡ : {Γ : Ctx C×D} {T : Ty Γ} → Tm Γ T → (c : Ob C) → Tm (Γ ⟨ c ⟩ˡ) (T ᵗʸ⟨ c ⟩ˡ)
fix-tmˡ t c ⟨ d , γ ⟩' = t ⟨ [ c , d ] , γ ⟩'
naturality (fix-tmˡ t _) _ _ = naturality t _ _

fix-tmʳ : {Γ : Ctx C×D} {T : Ty Γ} → Tm Γ T → (d : Ob D) → Tm (Γ ⟨ d ⟩ʳ) (T ᵗʸ⟨ d ⟩ʳ)
fix-tmʳ t d ⟨ c , γ ⟩' = t ⟨ [ c , d ] , γ ⟩'
naturality (fix-tmʳ t _) _ _ = naturality t _ _

_ᵗᵐ⟨_⟩ˡ : {Γ : Ctx C×D} {T : Ty Γ} → Tm Γ T → (c : Ob C) → Tm (Γ ⟨ c ⟩ˡ) (T ᵗʸ⟨ c ⟩ˡ)
t ᵗᵐ⟨ c ⟩ˡ = fix-tmˡ t c

_ᵗᵐ⟨_⟩ʳ : {Γ : Ctx C×D} {T : Ty Γ} → Tm Γ T → (d : Ob D) → Tm (Γ ⟨ d ⟩ʳ) (T ᵗʸ⟨ d ⟩ʳ)
t ᵗᵐ⟨ d ⟩ʳ = fix-tmʳ t d

fix-tm-tm-congˡ : {Γ : Ctx C×D} {T : Ty Γ} {t t' : Tm Γ T} {c : Ob C} → 
                  t ≅ᵗᵐ t' → t ᵗᵐ⟨ c ⟩ˡ ≅ᵗᵐ t' ᵗᵐ⟨ c ⟩ˡ
eq (fix-tm-tm-congˡ t=t') _ = eq t=t' _

fix-tm-tm-congʳ : {Γ : Ctx C×D} {T : Ty Γ} {t t' : Tm Γ T} {d : Ob D} → 
                  t ≅ᵗᵐ t' → t ᵗᵐ⟨ d ⟩ʳ ≅ᵗᵐ t' ᵗᵐ⟨ d ⟩ʳ
eq (fix-tm-tm-congʳ t=t') _ = eq t=t' _
