--------------------------------------------------
-- Contexts over product base categories
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.ContextProdBase {C D : BaseCategory} where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Data.Product renaming (_,_ to [_,_])
open import Model.CwF-Structure.Context

open BaseCategory

private
  C×D : BaseCategory
  C×D = C ⊗ D
  
  variable
    c c₁ c₂ c₃ : Ob C
    d d₁ d₂ d₃ : Ob D
    Δ Γ Θ : Ctx C×D

infix 30 _⟨_⟩ˡ _⟨_⟩ʳ
infix 30 _⟪_⟫ˡ _⟪_⟫ʳ
infix 30 _ˢ⟨_⟩ˡ _ˢ⟨_⟩ʳ

--------------------------------------------------
-- Functions related to contexts over a product base category C ⊗ D

-- Fix an object c in C and restrict a context over C×D to a context over D
fix-ctxˡ : Ctx C×D → Ob C → Ctx D
fix-ctxˡ Γ c ⟨ d ⟩ = Γ ⟨ [ c , d ] ⟩
fix-ctxˡ Γ c ⟪ g ⟫ γ = Γ ⟪ [ hom-id C {c} , g ] ⟫ γ
ctx-id (fix-ctxˡ Γ c) = ctx-id Γ
ctx-comp (fix-ctxˡ Γ c) {γ = γ} = trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ sym (hom-idˡ C) , refl ])) (ctx-comp Γ)

-- Fix an object d in D and restrict a context over C×D to a context over C
fix-ctxʳ : Ctx C×D → Ob D → Ctx C
fix-ctxʳ Γ d ⟨ c ⟩ = Γ ⟨ [ c , d ] ⟩
fix-ctxʳ Γ d ⟪ f ⟫ γ = Γ ⟪ [ f , hom-id D {d} ] ⟫ γ
ctx-id (fix-ctxʳ Γ d) = ctx-id Γ
ctx-comp (fix-ctxʳ Γ d) {γ = γ} = trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (hom-idˡ D) ])) (ctx-comp Γ)

-- Alternative syntax for `fix-ctxˡ` and `fix-ctxʳ`
-- `ˡ` and `ʳ` indicate the direction of the restriction
_⟨_⟩ˡ : Ctx C×D → Ob C  → Ctx D
Γ ⟨ c ⟩ˡ = fix-ctxˡ Γ c

_⟨_⟩ʳ : Ctx C×D → Ob D → Ctx C
Γ ⟨ d ⟩ʳ = fix-ctxʳ Γ d

-- Given a morphism f : c₁ → c₂ in C, construct a subsitution from Γ ⟨ c₂ ⟩ˡ to Γ ⟨ c₁ ⟩ˡ
const-substˡ : (Γ : Ctx C×D) → (Hom C c₁ c₂) → Γ ⟨ c₂ ⟩ˡ ⇒ Γ ⟨ c₁ ⟩ˡ
func (const-substˡ Γ f) = Γ ⟪ [ f , hom-id D ] ⟫_
naturality (const-substˡ Γ f) {f = g} {δ = δ} = 
  trans (sym (ctx-comp Γ))
  (trans (cong (Γ ⟪_⟫ δ) (×-≡,≡→≡ [ hom-idⁱ C , hom-idᵒ D ]))
         (ctx-comp Γ))

-- Given a morphism g : d₁ → d₂ in D, construct a subsitution from Γ ⟨ d₂ ⟩ʳ to Γ ⟨ d₁ ⟩ʳ
const-substʳ : (Γ : Ctx C×D) → (Hom D d₁ d₂) → Γ ⟨ d₂ ⟩ʳ ⇒ Γ ⟨ d₁ ⟩ʳ
func (const-substʳ Γ g) = Γ ⟪ [ hom-id C , g ] ⟫_
naturality (const-substʳ Γ g) {f = f} {δ = δ} = 
  trans (sym (ctx-comp Γ))
  (trans (cong (Γ ⟪_⟫ δ) (×-≡,≡→≡ [ hom-idᵒ C , hom-idⁱ D ]))
         (ctx-comp Γ))

-- Alternative syntax for `const-substˡ` and `const-substʳ`
_⟪_⟫ˡ : (Γ : Ctx C×D) → (Hom C c₁ c₂) → Γ ⟨ c₂ ⟩ˡ ⇒ Γ ⟨ c₁ ⟩ˡ
Γ ⟪ f ⟫ˡ = const-substˡ Γ f

_⟪_⟫ʳ : (Γ : Ctx C×D) → (Hom D d₁ d₂) → Γ ⟨ d₂ ⟩ʳ ⇒ Γ ⟨ d₁ ⟩ʳ
Γ ⟪ g ⟫ʳ = const-substʳ Γ g

-- `_⟪_⟫ˡ` respects the identity substitution
≅ˢ-id-const-substˡ : {Γ : Ctx C×D} → Γ ⟪ hom-id C ⟫ˡ ≅ˢ id-subst (Γ ⟨ c ⟩ˡ)
eq (≅ˢ-id-const-substˡ {Γ = Γ}) γ = ctx-id Γ

-- `_⟪_⟫ʳ` respects the identity substitution
≅ˢ-id-const-substʳ : {Γ : Ctx C×D} → Γ ⟪ hom-id D ⟫ʳ ≅ˢ id-subst (Γ ⟨ d ⟩ʳ)
eq (≅ˢ-id-const-substʳ {Γ = Γ}) γ = ctx-id Γ

-- `_⟪_⟫ˡ` respects euqalities of morphisms in C
≅ˢ-cong-const-substˡ : {Γ : Ctx C×D} {f₁ f₂ : Hom C c₁ c₂} → f₁ ≡ f₂ → Γ ⟪ f₁ ⟫ˡ ≅ˢ Γ ⟪ f₂ ⟫ˡ
eq (≅ˢ-cong-const-substˡ {Γ = Γ} e-hom) γ = cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ e-hom , refl ])

-- `_⟪_⟫ʳ` respects euqalities of morphisms in D
≅ˢ-cong-const-substʳ : {Γ : Ctx C×D} {g₁ g₂ : Hom D d₁ d₂} → g₁ ≡ g₂ → Γ ⟪ g₁ ⟫ʳ ≅ˢ Γ ⟪ g₂ ⟫ʳ
eq (≅ˢ-cong-const-substʳ {Γ = Γ} e-hom) γ = cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , e-hom ])

-- `_⟪_⟫ˡ` respects composition of substitutions
⊚-comp-const-substˡ : {Γ : Ctx C×D} → (f₁ : Hom C c₁ c₂) → (f₂ : Hom C c₂ c₃) → 
                       Γ ⟪ f₂ ∙[ C ] f₁ ⟫ˡ ≅ˢ Γ ⟪ f₁ ⟫ˡ ⊚ Γ ⟪ f₂ ⟫ˡ
eq (⊚-comp-const-substˡ {Γ = Γ} f₁ f₂) γ = trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ refl , sym (hom-idˡ D) ])) (ctx-comp Γ)
  -- RHS: func (Γ ⟪ f₂ ∙[ C ] f₁ ⟫ˡ) {d} γ ≡ func (Γ ⟪ f₁ ⟫ˡ) (func (Γ ⟪ f₂ ⟫ˡ) γ)
  -- Γ ⟪ [ f₂ ∙[ C ] f₁ , hom-id D {d} ] ⟫ γ ≡ Γ ⟪ [ f₁ , hom-id D {d} ] ⟫ (Γ ⟪ [ f₂ , hom-id D {d} ] ⟫ γ)

-- `_⟪_⟫ʳ` respects composition of substitutions
⊚-comp-const-substʳ : {Γ : Ctx C×D} → (g₁ : Hom D d₁ d₂) → (g₂ : Hom D d₂ d₃) → 
  Γ ⟪ g₂ ∙[ D ] g₁ ⟫ʳ ≅ˢ Γ ⟪ g₁ ⟫ʳ ⊚ Γ ⟪ g₂ ⟫ʳ
eq (⊚-comp-const-substʳ {Γ = Γ} g₁ g₂) γ = trans (cong (Γ ⟪_⟫ γ) (×-≡,≡→≡ [ sym (hom-idˡ C) , refl ])) (ctx-comp Γ)

-- Restrict a substitution in C×D to a substitution in D
fix-substˡ : {Δ Γ : Ctx C×D} → (σ : Δ ⇒ Γ) → (c : Ob C) → Δ ⟨ c ⟩ˡ ⇒ Γ ⟨ c ⟩ˡ
func (fix-substˡ σ c) {d} = func σ {[ c , d ]}
naturality (fix-substˡ σ c) = naturality σ

-- Restrict a substitution in C×D to a substitution in C
fix-substʳ : {Δ Γ : Ctx C×D} → (σ : Δ ⇒ Γ) → (d : Ob D) → Δ ⟨ d ⟩ʳ ⇒ Γ ⟨ d ⟩ʳ
func (fix-substʳ σ d) {c} = func σ {[ c , d ]}
naturality (fix-substʳ σ c) = naturality σ

-- Alternative syntax for `fix-substˡ` and `fix-substʳ`
_ˢ⟨_⟩ˡ : {Δ Γ : Ctx C×D} → (σ : Δ ⇒ Γ) → (c : Ob C) → Δ ⟨ c ⟩ˡ ⇒ Γ ⟨ c ⟩ˡ
σ ˢ⟨ c ⟩ˡ = fix-substˡ σ c

_ˢ⟨_⟩ʳ : {Δ Γ : Ctx C×D} → (σ : Δ ⇒ Γ) → (d : Ob D) → Δ ⟨ d ⟩ʳ ⇒ Γ ⟨ d ⟩ʳ
σ ˢ⟨ d ⟩ʳ = fix-substʳ σ d

-- `_ˢ⟨_⟩ˡ` and `_⟪_⟫ˡ` commute.
fix-const-substˡ : {Δ Γ : Ctx C×D} (σ : Δ ⇒ Γ) {f : Hom C c₁ c₂} → 
                   (Γ ⟪ f ⟫ˡ) ⊚ (σ ˢ⟨ c₂ ⟩ˡ) ≅ˢ (σ ˢ⟨ c₁ ⟩ˡ) ⊚ (Δ ⟪ f ⟫ˡ)
eq (fix-const-substˡ σ) γ = naturality σ

-- `_ˢ⟨_⟩ʳ` and `_⟪_⟫ʳ` commute.
fix-const-substʳ : {Δ Γ : Ctx C×D} (σ : Δ ⇒ Γ) {g : Hom D d₁ d₂} → 
                   (Γ ⟪ g ⟫ʳ) ⊚ (σ ˢ⟨ d₂ ⟩ʳ) ≅ˢ (σ ˢ⟨ d₁ ⟩ʳ) ⊚ (Δ ⟪ g ⟫ʳ)
eq (fix-const-substʳ σ) γ = naturality σ

-- `_ˢ⟨_⟩ˡ` respects equivalence of substitutions.
fix-subst-congˡ : {Δ Γ : Ctx C×D} {σ τ : Δ ⇒ Γ} {c : Ob C} → σ ≅ˢ τ → σ ˢ⟨ c ⟩ˡ ≅ˢ τ ˢ⟨ c ⟩ˡ
eq (fix-subst-congˡ σ=τ) = eq σ=τ

-- `_ˢ⟨_⟩ʳ` respects equivalence of substitutions.
fix-subst-congʳ : {Δ Γ : Ctx C×D} {σ τ : Δ ⇒ Γ} {d : Ob D} → σ ≅ˢ τ → σ ˢ⟨ d ⟩ʳ ≅ˢ τ ˢ⟨ d ⟩ʳ
eq (fix-subst-congʳ σ=τ) = eq σ=τ

-- `_ˢ⟨_⟩ˡ` preserves identity subsitutions.
fix-subst-idˡ : {Γ : Ctx C×D} → (id-subst Γ) ˢ⟨ c ⟩ˡ ≅ˢ id-subst (Γ ⟨ c ⟩ˡ)
eq fix-subst-idˡ γ = refl

-- `_ˢ⟨_⟩ʳ` preserves identity subsitutions.
fix-subst-idʳ : {Γ : Ctx C×D} → (id-subst Γ) ˢ⟨ d ⟩ʳ ≅ˢ id-subst (Γ ⟨ d ⟩ʳ)
eq fix-subst-idʳ γ = refl

-- `_ˢ⟨_⟩ˡ` commutes with composition of substitutions.
fix-subst-⊚ˡ : {Δ Γ Θ : Ctx C×D} {c : Ob C} → (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → 
               (τ ⊚ σ) ˢ⟨ c ⟩ˡ ≅ˢ (τ ˢ⟨ c ⟩ˡ) ⊚ (σ ˢ⟨ c ⟩ˡ)
eq (fix-subst-⊚ˡ τ σ) γ = refl

-- `_ˢ⟨_⟩ʳ` commutes with composition of substitutions.
fix-subst-⊚ʳ : {Δ Γ Θ : Ctx C×D} {d : Ob D} → (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → 
               (τ ⊚ σ) ˢ⟨ d ⟩ʳ ≅ˢ (τ ˢ⟨ d ⟩ʳ) ⊚ (σ ˢ⟨ d ⟩ʳ)
eq (fix-subst-⊚ʳ τ σ) γ = refl

eγ-decompnˡ : (Γ : Ctx C×D) → {f : Hom C c₁ c₂} {g : Hom D d₁ d₂} →
              {γ₁ : Γ ⟨ [ c₁ , d₁ ] ⟩} {γ₂ : Γ ⟨ [ c₂ , d₂ ] ⟩} → 
              (eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁) → 
              Γ ⟨ c₁ ⟩ˡ ⟪ g ⟫ (Γ ⟨ d₂ ⟩ʳ ⟪ f ⟫ γ₂) ≡ γ₁
eγ-decompnˡ {c₁ = c₁} {d₂ = d₂} Γ {f} {g} {γ₁} {γ₂} eγ = 
  begin 
    Γ ⟨ c₁ ⟩ˡ ⟪ g ⟫ (Γ ⟨ d₂ ⟩ʳ ⟪ f ⟫ γ₂)
  ≡˘⟨ ctx-comp Γ ⟩
    Γ ⟪ [ _∙_ C f (hom-id C) , _∙_ D (hom-id D) g ] ⟫ γ₂
  ≡⟨ cong (Γ ⟪_⟫ γ₂) (×-≡,≡→≡ [ hom-idʳ C , hom-idˡ D ]) ⟩
    Γ ⟪ [ f , g ] ⟫ γ₂ 
  ≡⟨ eγ ⟩ 
    γ₁ ∎
  where open ≡-Reasoning

eγ-decompnʳ : (Γ : Ctx C×D) → {f : Hom C c₁ c₂} {g : Hom D d₁ d₂} →
              {γ₁ : Γ ⟨ [ c₁ , d₁ ] ⟩} {γ₂ : Γ ⟨ [ c₂ , d₂ ] ⟩} → 
              (eγ : Γ ⟪ [ f , g ] ⟫ γ₂ ≡ γ₁) → 
              Γ ⟨ d₁ ⟩ʳ ⟪ f ⟫ (Γ ⟨ c₂ ⟩ˡ ⟪ g ⟫ γ₂) ≡ γ₁
eγ-decompnʳ {c₂ = c₂} {d₁ = d₁} Γ {f} {g} {γ₁} {γ₂} eγ =
  begin
    Γ ⟨ d₁ ⟩ʳ ⟪ f ⟫ (Γ ⟨ c₂ ⟩ˡ ⟪ g ⟫ γ₂)
  ≡˘⟨ ctx-comp Γ ⟩
    Γ ⟪ [ _∙_ C (hom-id C) f , _∙_ D g (hom-id D) ] ⟫ γ₂
  ≡⟨ cong (Γ ⟪_⟫ γ₂) (×-≡,≡→≡ [ hom-idˡ C , hom-idʳ D ]) ⟩
    Γ ⟪ [ f , g ] ⟫ γ₂
  ≡⟨ eγ ⟩
    γ₁ ∎
  where open ≡-Reasoning
