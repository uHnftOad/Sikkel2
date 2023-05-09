--------------------------------------------------
-- Types in contexts over product base categories
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.TypeProdBase {C D : BaseCategory} where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Data.Product renaming (_,_ to [_,_])

open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextProdBase

open BaseCategory

private
  C×D : BaseCategory
  C×D = C ⊗ D
  
  variable
    c c₁ c₂ c₃ : Ob C
    d d₁ d₂ d₃ : Ob D
    Γ Δ Θ : Ctx C×D
    T : Ty Γ

infix 30 _ᵗʸ⟨_⟩ˡ _ᵗʸ⟨_⟩ʳ


--------------------------------------------------
-- Restrict a type in a context over C×D to a type in a context over D
fix-tyˡ : {Γ : Ctx C×D} → Ty Γ → (c : Ob C) → Ty (Γ ⟨ c ⟩ˡ)
fix-tyˡ T c ⟨ d , γ ⟩ = T ⟨ [ c , d ] , γ ⟩
fix-tyˡ T c ⟪ g , eγ ⟫ t = T ⟪ [ hom-id C , g ] , eγ ⟫ t
ty-cong (fix-tyˡ T c) e-hom = ty-cong T (×-≡,≡→≡ [ refl , e-hom ])
ty-id (fix-tyˡ T c) = ty-id T
ty-comp (fix-tyˡ T c) = trans (ty-cong T (×-≡,≡→≡ [ sym (hom-idˡ C) , refl ])) (ty-comp T)

-- Restrict a type in a context over C×D to a type in a context over C
fix-tyʳ : {Γ : Ctx C×D} → Ty Γ → (d : Ob D) → Ty (Γ ⟨ d ⟩ʳ)
fix-tyʳ T d ⟨ c , γ ⟩ = T ⟨ [ c , d ] , γ ⟩
fix-tyʳ T d ⟪ f , eγ ⟫ t = T ⟪ [ f , hom-id D ] , eγ ⟫ t
ty-cong (fix-tyʳ T d) e-hom = ty-cong T (×-≡,≡→≡ [ e-hom , refl ])
ty-id (fix-tyʳ T d) = ty-id T
ty-comp (fix-tyʳ T d) = trans (ty-cong T (×-≡,≡→≡ [ refl , sym (hom-idˡ D) ])) (ty-comp T)

-- Alternative syntax for fix-tyˡ and fix-tyʳ
-- `ˡ` and `ʳ` indicate the direction of the restriction
_ᵗʸ⟨_⟩ˡ : {Γ : Ctx C×D} → Ty Γ → (c : Ob C) → Ty (Γ ⟨ c ⟩ˡ)
T ᵗʸ⟨ c ⟩ˡ = fix-tyˡ T c

_ᵗʸ⟨_⟩ʳ : {Γ : Ctx C×D} → Ty Γ → (d : Ob D) → Ty (Γ ⟨ d ⟩ʳ)
T ᵗʸ⟨ d ⟩ʳ = fix-tyʳ T d

ty-fix-ty-congˡ : {Γ : Ctx C×D} {T S : Ty Γ} → T ≅ᵗʸ S → (c : Ob C) → T ᵗʸ⟨ c ⟩ˡ ≅ᵗʸ S ᵗʸ⟨ c ⟩ˡ
func (from (ty-fix-ty-congˡ T=S c)) {d} = func (from T=S) {[ c , d ]}
_↣_.naturality (from (ty-fix-ty-congˡ T=S c)) = _↣_.naturality (from T=S)
func (to (ty-fix-ty-congˡ T=S c)) {d} = func (to T=S) {[ c , d ]}
_↣_.naturality (to (ty-fix-ty-congˡ T=S c)) = _↣_.naturality (to T=S)
eq (isoˡ (ty-fix-ty-congˡ T=S c)) = eq (isoˡ T=S) 
eq (isoʳ (ty-fix-ty-congˡ T=S c)) = eq (isoʳ T=S) 

ty-fix-ty-congʳ : {Γ : Ctx C×D} {T S : Ty Γ} → T ≅ᵗʸ S → (d : Ob D) → T ᵗʸ⟨ d ⟩ʳ ≅ᵗʸ S ᵗʸ⟨ d ⟩ʳ
func (from (ty-fix-ty-congʳ T=S d)) {c} = func (from T=S) {[ c , d ]}
_↣_.naturality (from (ty-fix-ty-congʳ T=S d)) = _↣_.naturality (from T=S)
func (to (ty-fix-ty-congʳ T=S d)) {c} = func (to T=S) {[ c , d ]}
_↣_.naturality (to (ty-fix-ty-congʳ T=S d)) = _↣_.naturality (to T=S)
eq (isoˡ (ty-fix-ty-congʳ T=S d)) = eq (isoˡ T=S)
eq (isoʳ (ty-fix-ty-congʳ T=S d)) = eq (isoʳ T=S)

mor-to-↣ˡ : {Γ : Ctx C×D} → (T : Ty Γ) → (f : Hom C c₁ c₂) → 
             T ᵗʸ⟨ c₂ ⟩ˡ ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ]
func (mor-to-↣ˡ T f) = T ᵗʸ⟨ _ ⟩ʳ ⟪ f , refl ⟫_
  -- refl : Γ ⟪ [ f , hom-id D {d} ] ⟫ γ ≡ Γ ⟪ [ f , hom-id D ] ⟫ γ
_↣_.naturality (mor-to-↣ˡ T f) = trans (sym (ty-comp T)) (trans (ty-cong T (×-≡,≡→≡ [ hom-idⁱ C , hom-idᵒ D ])) (ty-comp T))

mor-to-↣ʳ : {Γ : Ctx C×D} → (T : Ty Γ) → (g : Hom D d₁ d₂) → 
             T ᵗʸ⟨ d₂ ⟩ʳ ↣ T ᵗʸ⟨ d₁ ⟩ʳ [ Γ ˢ⟪ g ⟫ʳ ]
func (mor-to-↣ʳ T g) = T ᵗʸ⟨ _ ⟩ˡ ⟪ g , refl ⟫_
_↣_.naturality (mor-to-↣ʳ T g) = trans (sym (ty-comp T)) (trans (ty-cong T (×-≡,≡→≡ [ hom-idᵒ C , hom-idⁱ D ])) (ty-comp T))

--------------------------------------------------
-- Potentially useful lemmas

helper-cong : {Γ : Ctx C×D} {T : Ty Γ} {f f' : Hom C c₁ c₂} → f ≡ f' → 
              T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ] ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f' ⟫ˡ ]
helper-cong {T = T} f=f' = ty-subst-cong-subst (≅ˢ-cong-const-substˡ f=f') (T ᵗʸ⟨ _ ⟩ˡ)

{-
                mor-to-↣ˡ f                             from (helper f=f')
  T ᵗʸ⟨ c₂ ⟩ˡ ↣↣↣↣↣↣↣↣↣↣↣ T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f ⟫ˡ ] ↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣ T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f' ⟫ˡ ]
  T ᵗʸ⟨ c₂ ⟩ˡ ↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣ T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ˢ⟪ f' ⟫ˡ ]
                                      mor-to-↣ˡ f'   
  The top and bottom arrows are equivalent. 
-}
mor-to-↣-congˡ : {Γ : Ctx C×D} {T : Ty Γ} {f f' : Hom C c₁ c₂} → (f=f' : f ≡ f') →
                 from (helper-cong f=f') ⊙ mor-to-↣ˡ T f ≅ⁿ mor-to-↣ˡ T f'
eq (mor-to-↣-congˡ {T = T} f=f') t = trans (sym (ty-comp T)) (ty-cong T (×-≡,≡→≡ [ trans (hom-idʳ C) f=f' , hom-idˡ D ]))

ty-fix-ty-idˡ : {Γ : Ctx C×D} {T : Ty Γ} {c : Ob C} → T ᵗʸ⟨ c ⟩ˡ [ Γ ˢ⟪ hom-id C ⟫ˡ ] ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ
ty-fix-ty-idˡ {T = T} = transᵗʸ (ty-subst-cong-subst ≅ˢ-id-const-substˡ (T ᵗʸ⟨ _ ⟩ˡ)) (ty-subst-id (T ᵗʸ⟨ _ ⟩ˡ))

mor-to-↣-idˡ : {Γ : Ctx C×D} {T : Ty Γ} {c : Ob C} → mor-to-↣ˡ {c₁ = c} {c₂ = c} T (hom-id C) ≅ⁿ to ty-fix-ty-idˡ
eq (mor-to-↣-idˡ {T = T}) t = ty-cong T refl

{-
              mor-to-↣ˡ (hom-id C)                                         from ty-fix-ty-idˡ
  T ᵗʸ⟨ c₂ ⟩ˡ ↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣ T ᵗʸ⟨ c₂ ⟩ˡ [ Γ ˢ⟪ hom-id C ⟫ˡ ] ↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣ T ᵗʸ⟨ c₂ ⟩ˡ

  T ᵗʸ⟨ c₂ ⟩ˡ ↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣↣ T ᵗʸ⟨ c₂ ⟩ˡ
                id-trans (T ᵗʸ⟨ c₂ ⟩ˡ)
-}
-- mor-to-↣-idˡ : {Γ : Ctx C×D} {T : Ty Γ} {c : Ob C} → from ty-fix-ty-idˡ ⊙ mor-to-↣ˡ T (hom-id C) ≅ⁿ id-trans (T ᵗʸ⟨ c ⟩ˡ)
-- eq (mor-to-↣-idˡ {T = T}) t = trans (sym (ty-comp T)) (trans (ty-cong T (×-≡,≡→≡ [ hom-idˡ C , hom-idˡ D ])) (ty-id T))
