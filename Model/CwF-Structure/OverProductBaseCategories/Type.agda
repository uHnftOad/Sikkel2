--------------------------------------------------
-- Types in contexts over product base categories
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.OverProductBaseCategories.Type {C D : BaseCategory} where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Data.Product renaming (_,_ to [_,_])
open import Function using (id; _∘_)

open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.OverProductBaseCategories.Context

open BaseCategory

private
  C×D : BaseCategory
  C×D = C ⊗ D
  
  variable
    c c₁ c₂ c₃ : Ob C
    d d₁ d₂ d₃ : Ob D
    Γ Δ Θ : Ctx C×D

infixl 30 _ᵗʸ⟨_⟩ˡ _ᵗʸ⟨_⟩ʳ
infixl 30 _ₙ⟨_⟩ˡ _ₙ⟨_⟩ʳ


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
_ᵗʸ⟨_⟩ˡ : {Γ : Ctx C×D} → Ty Γ → (c : Ob C) → Ty (Γ ⟨ c ⟩ˡ)
T ᵗʸ⟨ c ⟩ˡ = fix-tyˡ T c

_ᵗʸ⟨_⟩ʳ : {Γ : Ctx C×D} → Ty Γ → (d : Ob D) → Ty (Γ ⟨ d ⟩ʳ)
T ᵗʸ⟨ d ⟩ʳ = fix-tyʳ T d

fix-ty-ty-congˡ : {Γ : Ctx C×D} {T S : Ty Γ} → T ≅ᵗʸ S → (c : Ob C) → T ᵗʸ⟨ c ⟩ˡ ≅ᵗʸ S ᵗʸ⟨ c ⟩ˡ
func (from (fix-ty-ty-congˡ T=S c)) {d} = func (from T=S) {[ c , d ]}
_↣_.naturality (from (fix-ty-ty-congˡ T=S c)) = _↣_.naturality (from T=S)
func (to (fix-ty-ty-congˡ T=S c)) {d} = func (to T=S) {[ c , d ]}
_↣_.naturality (to (fix-ty-ty-congˡ T=S c)) = _↣_.naturality (to T=S)
eq (isoˡ (fix-ty-ty-congˡ T=S c)) = eq (isoˡ T=S) 
eq (isoʳ (fix-ty-ty-congˡ T=S c)) = eq (isoʳ T=S) 

fix-ty-ty-congʳ : {Γ : Ctx C×D} {T S : Ty Γ} → T ≅ᵗʸ S → (d : Ob D) → T ᵗʸ⟨ d ⟩ʳ ≅ᵗʸ S ᵗʸ⟨ d ⟩ʳ
func (from (fix-ty-ty-congʳ T=S d)) {c} = func (from T=S) {[ c , d ]}
_↣_.naturality (from (fix-ty-ty-congʳ T=S d)) = _↣_.naturality (from T=S)
func (to (fix-ty-ty-congʳ T=S d)) {c} = func (to T=S) {[ c , d ]}
_↣_.naturality (to (fix-ty-ty-congʳ T=S d)) = _↣_.naturality (to T=S)
eq (isoˡ (fix-ty-ty-congʳ T=S d)) = eq (isoˡ T=S)
eq (isoʳ (fix-ty-ty-congʳ T=S d)) = eq (isoʳ T=S)

fix-ty-idˡ : {Γ : Ctx C×D} {T : Ty Γ} {c : Ob C} → T ᵗʸ⟨ c ⟩ˡ [ Γ ⟪ hom-id C ⟫ˡ ] ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ
fix-ty-idˡ {T = T} = transᵗʸ (ty-subst-cong-subst ≅ˢ-id-const-substˡ (T ᵗʸ⟨ _ ⟩ˡ)) (ty-subst-id (T ᵗʸ⟨ _ ⟩ˡ))

fix-ty-idʳ : {Γ : Ctx C×D} {T : Ty Γ} {d : Ob D} → T ᵗʸ⟨ d ⟩ʳ [ Γ ⟪ hom-id D ⟫ʳ ] ≅ᵗʸ T ᵗʸ⟨ d ⟩ʳ
fix-ty-idʳ {T = T} = transᵗʸ (ty-subst-cong-subst ≅ˢ-id-const-substʳ (T ᵗʸ⟨ _ ⟩ʳ)) (ty-subst-id (T ᵗʸ⟨ _ ⟩ʳ))

fix-ty-mor-congˡ : {Γ : Ctx C×D} {T : Ty Γ} {f f' : Hom C c₁ c₂} → f ≡ f' → 
                    T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ⟪ f ⟫ˡ ] ≅ᵗʸ T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ⟪ f' ⟫ˡ ]
fix-ty-mor-congˡ {T = T} f=f' = ty-subst-cong-subst (≅ˢ-cong-const-substˡ f=f') (T ᵗʸ⟨ _ ⟩ˡ)

fix-ty-mor-congʳ : {Γ : Ctx C×D} {T : Ty Γ} {f f' : Hom D d₁ d₂} → f ≡ f' → 
                    T ᵗʸ⟨ d₁ ⟩ʳ [ Γ ⟪ f ⟫ʳ ] ≅ᵗʸ T ᵗʸ⟨ d₁ ⟩ʳ [ Γ ⟪ f' ⟫ʳ ]
fix-ty-mor-congʳ {T = T} f=f' = ty-subst-cong-subst (≅ˢ-cong-const-substʳ f=f') (T ᵗʸ⟨ _ ⟩ʳ)

fix-ty-subst-naturalˡ : {Δ Γ : Ctx C×D} {T : Ty Γ} {σ : Δ ⇒ Γ} {c : Ob C} →
                        (T [ σ ]) ᵗʸ⟨ c ⟩ˡ ≅ᵗʸ T ᵗʸ⟨ c ⟩ˡ [ σ ˢ⟨ c ⟩ˡ ]
func (from fix-ty-subst-naturalˡ) = id
_↣_.naturality (from fix-ty-subst-naturalˡ) = refl
func (to fix-ty-subst-naturalˡ) = id
_↣_.naturality (to fix-ty-subst-naturalˡ) = refl
eq (isoˡ fix-ty-subst-naturalˡ) t = refl
eq (isoʳ fix-ty-subst-naturalˡ) t = refl

fix-ty-subst-naturalʳ : {Δ Γ : Ctx C×D} {T : Ty Γ} {σ : Δ ⇒ Γ} {d : Ob D} →
                        (T [ σ ]) ᵗʸ⟨ d ⟩ʳ ≅ᵗʸ T ᵗʸ⟨ d ⟩ʳ [ σ ˢ⟨ d ⟩ʳ ]
func (from fix-ty-subst-naturalʳ) = id
_↣_.naturality (from fix-ty-subst-naturalʳ) = refl
func (to fix-ty-subst-naturalʳ) = id
_↣_.naturality (to fix-ty-subst-naturalʳ) = refl
eq (isoˡ fix-ty-subst-naturalʳ) t = refl
eq (isoʳ fix-ty-subst-naturalʳ) t = refl

--------------------------------------------------
-- Turn a morphism in a base category into a morphism between types

mor-to-↣ˡ : {Γ : Ctx C×D} → (T : Ty Γ) → (f : Hom C c₁ c₂) → 
             T ᵗʸ⟨ c₂ ⟩ˡ ↣ T ᵗʸ⟨ c₁ ⟩ˡ [ Γ ⟪ f ⟫ˡ ]
func (mor-to-↣ˡ T f) {d} = T ᵗʸ⟨ d ⟩ʳ ⟪ f , refl ⟫_
_↣_.naturality (mor-to-↣ˡ T f) = trans (sym (ty-comp T)) (trans (ty-cong T (×-≡,≡→≡ [ hom-idⁱ C , hom-idᵒ D ])) (ty-comp T))

mor-to-↣ʳ : {Γ : Ctx C×D} (T : Ty Γ) (g : Hom D d₁ d₂) → T ᵗʸ⟨ d₂ ⟩ʳ ↣ T ᵗʸ⟨ d₁ ⟩ʳ [ Γ ⟪ g ⟫ʳ ]
func (mor-to-↣ʳ T g) = T ᵗʸ⟨ _ ⟩ˡ ⟪ g , refl ⟫_
_↣_.naturality (mor-to-↣ʳ T g) = trans (sym (ty-comp T)) (trans (ty-cong T (×-≡,≡→≡ [ hom-idᵒ C , hom-idⁱ D ])) (ty-comp T))

mor-to-↣-idˡ : {Γ : Ctx C×D} {T : Ty Γ} {c : Ob C} → mor-to-↣ˡ {c₁ = c} {c₂ = c} T (hom-id C) ≅ⁿ to fix-ty-idˡ
eq (mor-to-↣-idˡ {T = T}) t = ty-cong T refl

mor-to-↣-idʳ : {Γ : Ctx C×D} {T : Ty Γ} {d : Ob D} → mor-to-↣ʳ {d₁ = d} {d₂ = d} T (hom-id D) ≅ⁿ to fix-ty-idʳ
eq (mor-to-↣-idʳ {T = T}) t = ty-cong T refl

mor-to-↣-congˡ : {Γ : Ctx C×D} {T : Ty Γ} {f f' : Hom C c₁ c₂} → (f=f' : f ≡ f') →
                  from (fix-ty-mor-congˡ f=f') ⊙ mor-to-↣ˡ T f ≅ⁿ mor-to-↣ˡ T f'
eq (mor-to-↣-congˡ {T = T} f=f') t = trans (sym (ty-comp T)) (ty-cong T (×-≡,≡→≡ [ trans (hom-idʳ C) f=f' , hom-idˡ D ]))


--------------------------------------------------
fix-ty-↣ˡ : {Γ : Ctx C×D} {T S : Ty Γ} → T ↣ S → (c : Ob C) → T ᵗʸ⟨ c ⟩ˡ ↣ S ᵗʸ⟨ c ⟩ˡ
func (fix-ty-↣ˡ η c) {d} {γ} = func η {[ c , d ]} {γ}
_↣_.naturality (fix-ty-↣ˡ η c) = _↣_.naturality η

fix-ty-↣ʳ : {Γ : Ctx C×D} {T S : Ty Γ} → T ↣ S → (d : Ob D) → T ᵗʸ⟨ d ⟩ʳ ↣ S ᵗʸ⟨ d ⟩ʳ
func (fix-ty-↣ʳ η d) {c} {γ} = func η {[ c , d ]} {γ}
_↣_.naturality (fix-ty-↣ʳ η d) = _↣_.naturality η

-- Alternative syntax for `fix-ty-↣ˡ` and `fix-ty-↣ʳ`
_ₙ⟨_⟩ˡ : {Γ : Ctx C×D} {T S : Ty Γ} → T ↣ S → (c : Ob C) → T ᵗʸ⟨ c ⟩ˡ ↣ S ᵗʸ⟨ c ⟩ˡ
η ₙ⟨ c ⟩ˡ = fix-ty-↣ˡ η c

_ₙ⟨_⟩ʳ : {Γ : Ctx C×D} {T S : Ty Γ} → T ↣ S → (d : Ob D) → T ᵗʸ⟨ d ⟩ʳ ↣ S ᵗʸ⟨ d ⟩ʳ
η ₙ⟨ d ⟩ʳ = fix-ty-↣ʳ η d

fix-ty-↣-idˡ : {Γ : Ctx C×D} {T : Ty Γ} {c : Ob C} → id-trans T ₙ⟨ c ⟩ˡ ≅ⁿ id-trans (T ᵗʸ⟨ c ⟩ˡ)
eq fix-ty-↣-idˡ t = refl

fix-ty-↣-idʳ : {Γ : Ctx C×D} {T : Ty Γ} {d : Ob D} → id-trans T ₙ⟨ d ⟩ʳ ≅ⁿ id-trans (T ᵗʸ⟨ d ⟩ʳ)
eq fix-ty-↣-idʳ t = refl

fix-ty-↣-compˡ : {Γ : Ctx C×D} {R T S : Ty Γ} {η : R ↣ T} {φ : T ↣ S} {c : Ob C} →
                  (φ ⊙ η) ₙ⟨ c ⟩ˡ ≅ⁿ φ ₙ⟨ c ⟩ˡ ⊙ η ₙ⟨ c ⟩ˡ
eq fix-ty-↣-compˡ t = refl

fix-ty-↣-compʳ : {Γ : Ctx C×D} {R T S : Ty Γ} {η : R ↣ T} {φ : T ↣ S} {d : Ob D} →
                  (φ ⊙ η) ₙ⟨ d ⟩ʳ ≅ⁿ φ ₙ⟨ d ⟩ʳ ⊙ η ₙ⟨ d ⟩ʳ
eq fix-ty-↣-compʳ t = refl

fix-ty-↣-congˡ : {Γ : Ctx C×D} {T S : Ty Γ} {η η' : T ↣ S} {c : Ob C} → η ≅ⁿ η' →
                  η ₙ⟨ c ⟩ˡ ≅ⁿ η' ₙ⟨ c ⟩ˡ
eq (fix-ty-↣-congˡ η=η') t = eq η=η' t

fix-ty-↣-congʳ : {Γ : Ctx C×D} {T S : Ty Γ} {η η' : T ↣ S} {d : Ob D} → η ≅ⁿ η' →
                  η ₙ⟨ d ⟩ʳ ≅ⁿ η' ₙ⟨ d ⟩ʳ
eq (fix-ty-↣-congʳ η=η') t = eq η=η' t
