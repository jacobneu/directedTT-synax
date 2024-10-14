{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality 

module PCwF where

open import CwF

infix 45 _⁻ᶜ _⁻ˢ _⁻ᵗ

postulate
  _⁻ᶜ : Con → Con
  _⁻ˢ : ∀{Δ Γ : Con} → Sub Δ Γ → Sub (Δ ⁻ᶜ) (Γ ⁻ᶜ)
  _⁻ᵗ : ∀{Γ} → Ty Γ → Ty Γ

-- variable
--   A B : Ty (Γ ⁻ᶜ)

postulate
  -- eqns for negation
  ◆⁻≡ : ◆ ⁻ᶜ ≡ ◆
  invC : ∀{Γ} → (Γ ⁻ᶜ) ⁻ᶜ ≡ Γ
  {-# REWRITE ◆⁻≡ invC #-}
  invS : ∀{Δ Γ}{σ : Sub Δ Γ} → (σ ⁻ˢ) ⁻ˢ ≡ σ
  invT : ∀{Γ}{C : Ty Γ} → (C ⁻ᵗ ) ⁻ᵗ ≡ C
  {-# REWRITE invS invT #-}

  id⁻≡ : ∀{Γ} →  (id {Γ = Γ}) ⁻ˢ ≡ id
  _∘⁻≡_ : ∀{Θ Δ Γ}(γ : Sub Δ Γ)(δ : Sub Θ Δ) → (γ ∘ δ) ⁻ˢ ≡ (γ ⁻ˢ) ∘ (δ ⁻ˢ)
  nat⁻ : ∀{Δ Γ C}(γ : Sub Δ Γ) → (C [ γ ]T) ⁻ᵗ ≡ (C ⁻ᵗ) [ γ ]T
  {-# REWRITE id⁻≡ _∘⁻≡_ nat⁻ #-} 

-- Minus CwF
Ty⁻ : Con → Type
Ty⁻ Γ = Ty (Γ ⁻ᶜ)
_[_]T⁻ : ∀{Δ Γ} → Ty⁻ Γ → Sub Δ Γ → Ty⁻ Δ
A [ γ ]T⁻ = A [ γ ⁻ˢ ]T
_[_∣_]T⁻ : ∀{Θ Δ Γ}(A : Ty⁻ Γ)(γ : Sub Δ Γ)(δ : Sub Θ Δ) → A [ γ ]T⁻ [ δ ]T⁻ ≡ A [ γ ∘ δ ]T⁻
A [ γ ∣ δ ]T⁻ = refl
_[id]T⁻ : ∀{Γ}(A : Ty⁻ Γ) → _[_]T⁻ {Δ = Γ} A id ≡ A
A [id]T⁻ = refl

Tm⁻ : (Γ : Con) → Ty⁻ Γ → Type
Tm⁻ Γ A = Tm (Γ ⁻ᶜ) (A ⁻ᵗ)
_[_]t⁻ : ∀{Δ Γ}{A : Ty⁻ Γ} → Tm⁻ Γ A → (γ : Sub Δ Γ) → Tm⁻ Δ (A [ γ ]T⁻)
a [ γ ]t⁻ = a [ γ ⁻ˢ ]t
_[_∣_]t⁻ : ∀{Δ Γ}{A : Ty⁻ Γ}(a : Tm⁻ Γ A)(γ : Sub Δ Γ)(δ : Sub Θ Δ) → _[_]t⁻ {A = A [ γ ]T⁻} (_[_]t⁻ {A = A} a γ) δ ≡ _[_]t⁻ {A = A} a (γ ∘ δ)
a [ γ ∣ δ ]t⁻ = refl
_[id]t⁻ : ∀{Γ A}(a : Tm⁻ Γ A) → _[_]t⁻ {Δ = Γ}{A = A} a id ≡ a
a [id]t⁻ = refl


_▷⁻_ : (Γ : Con) → Ty⁻ Γ → Con
Γ ▷⁻ A = ( (Γ ⁻ᶜ) ▷ (A ⁻ᵗ) ) ⁻ᶜ
_,₋_ : ∀{Δ Γ A}(σ : Sub Δ Γ) → Tm⁻ Δ (A [ σ ]T⁻) → Sub Δ (Γ ▷⁻ A)
σ ,₋ t = (σ ⁻ˢ ,₊ t) ⁻ˢ
,-S : ∀{Δ Γ A}(σ : Sub Δ Γ) → (t : Tm⁻ Δ (A [ σ ]T⁻)) → (_,₋_ {A = A} σ t) ⁻ˢ ≡  (σ ⁻ˢ ,₊ t)
,-S σ t = invS 
{-# REWRITE ,-S #-}
π₁₋ : ∀{Δ Γ A}(τ : Sub Δ (Γ ▷⁻ A)) → Sub Δ Γ
π₁₋ τ = (π₁ (τ ⁻ˢ)) ⁻ˢ
π₁-S : ∀{Δ Γ A}(τ : Sub Δ (Γ ▷⁻ A)) → (π₁₋ {Δ = Δ}{Γ = Γ}{A = A} τ) ⁻ˢ ≡ π₁ {Δ = Δ ⁻ᶜ}{Γ = Γ ⁻ᶜ}{C = A ⁻ᵗ} (τ ⁻ˢ)
π₁-S τ = invS
{-# REWRITE π₁-S #-} 
π₂₋ : ∀{Δ Γ A}(τ : Sub Δ (Γ ▷⁻ A)) → Tm⁻ Δ (A [ π₁₋ {Δ = Δ}{Γ = Γ}{A = A} τ ]T⁻)
π₂₋ τ = π₂ (τ ⁻ˢ)

▷β₁₋ : ∀{Δ Γ A}{σ : Sub Δ Γ}{t : Tm⁻ Δ (A [ σ ]T⁻)} → π₁₋ {A = A} (_,₋_ {A = A} σ t) ≡ σ
▷β₁₋ = refl
▷β₂₋ : ∀{Δ Γ A}{σ : Sub Δ Γ}{t : Tm⁻ Δ (A [ σ ]T⁻)} → π₂₋ {Γ = Γ}{A = A} (_,₋_ {A = A} σ t) ≡ t
▷β₂₋ = refl
▷η₋ : ∀{Δ Γ A}{τ : Sub Δ (Γ ▷⁻ A)} → _,₋_ {A = A} (π₁₋ {Γ = Γ}{A = A} τ) (π₂₋ {Γ = Γ}{A = A} τ) ≡ τ
▷η₋ = invS
π₁₋∘ : ∀{Δ Γ A}{τ : Sub Δ (Γ ▷⁻ A)}{Θ}{δ : Sub Θ Δ} → π₁₋ {Γ = Γ}{A = A} (τ ∘ δ) ≡ π₁₋ {A = A} τ ∘ δ
π₁₋∘ = refl
π₂₋[] : ∀{Δ Γ A}{τ : Sub Δ (Γ ▷⁻ A)}{Θ}{δ : Sub Θ Δ} → 
    -- (π₂₋ τ)[ δ ]t⁻ ≡ π₂₋ (τ ∘ δ)
    _[_]t⁻ {A = _[_]T⁻ {Γ = Γ} A (π₁₋ {A = A} τ)}(π₂₋ {Γ = Γ}{A = A} τ) δ  ≡ π₂₋ {Δ = Θ}{Γ = Γ}{A = A} (τ ∘ δ)
π₂₋[] = refl


p₋ : ∀{Γ A} → Sub (Γ ▷⁻ A) Γ
p₋ {Γ}{A} = π₁₋ {A = A} (id {Γ = Γ ▷⁻ A})
v₋ : ∀{Γ A} → Tm⁻ (Γ ▷⁻ A) (_[_]T⁻ {Γ = Γ} A (p₋ {A = A}))
v₋ {Γ}{A} = π₂₋ {Γ = Γ}{A = A} id
_^⁻_ : ∀{Δ Γ}(σ : Sub Δ Γ)(A : Ty⁻ Γ) → Sub (Δ ▷⁻ A [ σ ]T⁻) (Γ ▷⁻ A)
_^⁻_ {Δ}{Γ}(σ)(A) = _,₋_ {Γ = Γ}{A = A} (σ ∘ p₋ {Γ = Δ}{A = A [ σ ]T⁻}) (v₋ {Γ = Δ}{A = A [ σ ]T⁻}) -- σ ∘ p ,₊ v
v₋↦ : ∀{Γ A} → Tm⁻ Γ A → Sub Γ (Γ ▷⁻ A)
v₋↦ {Γ}{A} t = _,₋_ {A = A} id t
v₋⟨_⟩↦ : ∀{Γ} → (A : Ty⁻ Γ) → Tm⁻ Γ A → Sub Γ (Γ ▷⁻ A)
v₋⟨_⟩↦ {Γ} A t = _,₋_ {A = A} id t



infixl 5 _▷⁻_
infixl 40 _[_]T⁻
infixl 40 _[_∣_]T⁻
infixl 40 _[id]T⁻ _[id]t⁻
infixl 41 v₋⟨_⟩↦
infixl 5 _,₋_
infixl 40 _[_]t⁻
infixl 40 _[_∣_]t⁻