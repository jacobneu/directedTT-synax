{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module CwF where

{-# BUILTIN REWRITE _≡_ #-}

Type = Set

postulate
  Con : Type
  Sub : Con → Con → Type
  Ty  : Con → Type
  Tm  : (Γ : Con) → Ty Γ → Type


variable
  Γ Δ Θ Ξ : Con
  γ : Sub Δ Γ
  δ : Sub Θ Δ
  θ : Sub Ξ Θ
  C D : Ty Γ
  c c' : Tm Γ C
  

postulate
  -- category
  _∘_         : ∀{Γ Θ Δ} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
  ass         : ∀{Ξ Δ Γ Θ} → (ϑ : Sub Ξ Θ)(δ : Sub Θ Δ)(γ : Sub Δ Γ) →
                (γ ∘ δ) ∘ ϑ ≡ γ ∘ (δ ∘ ϑ)
  id          : ∀{Γ} → Sub Γ Γ
  idl         : ∀{Γ Δ}(γ : Sub Δ Γ) → id ∘ γ ≡ γ
  idr         : ∀{Γ Δ}(γ : Sub Δ Γ) → γ ∘ id ≡ γ
  {-# REWRITE ass idl idr #-}
  
  -- terminal object
  ◆           : Con
  ε           : ∀{Γ} → Sub Γ ◆
  ◆η          : ∀{Γ}(σ : Sub Γ ◆) → σ ≡ ε
  
  -- a family structure
  _[_]T       : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ
  _[_∣_]T     : ∀{Θ Δ Γ}(C : Ty Γ)(γ : Sub Δ Γ)(δ : Sub Θ Δ) →
                C [ γ ]T [ δ ]T ≡ C [ γ ∘ δ ]T
  _[id]T      : ∀{Γ}(C : Ty Γ) → C [ id ]T ≡ C
  {-# REWRITE _[_∣_]T _[id]T #-}
  _[_]t       : ∀{Δ Γ}{C : Ty Γ} → Tm Γ C → (γ : Sub Δ Γ) → Tm Δ (C [ γ ]T)
  _[_∣_]t     : c [ γ ]t [ δ ]t ≡ c [ γ ∘ δ ]t
  _[id]t      : c [ id ]t ≡ c
  {-# REWRITE _[_∣_]t _[id]t #-}

  -- extend a Con with a Ty
  _▷_         : (Γ : Con) → Ty Γ → Con
  _,₊_        : ∀{Δ Γ C}(σ : Sub Δ Γ) → Tm Δ (C [ σ ]T) → Sub Δ (Γ ▷ C)
  π₁          : ∀{Δ Γ C}(τ : Sub Δ (Γ ▷ C)) → Sub Δ Γ
  π₂          : ∀{Δ Γ C}(τ : Sub Δ (Γ ▷ C)) → Tm Δ (C [ π₁ τ ]T)
  ▷β₁         : ∀{Δ Γ C}{σ : Sub Δ Γ}{t : Tm Δ (C [ σ ]T)} → π₁ (_,₊_ {C = C} σ t) ≡ σ
  {-# REWRITE ▷β₁ #-}
  ▷β₂         : ∀{Δ Γ C}{σ : Sub Δ Γ}{t : Tm Δ (C [ σ ]T)} → π₂ (_,₊_ {C = C} σ t) ≡ t
  ▷η          : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)} → π₁ τ ,₊ π₂ τ ≡ τ
  π₁∘         : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)}{Θ}{δ : Sub Θ Δ} → π₁ (τ ∘ δ) ≡ π₁ τ ∘ δ
  {-# REWRITE ▷β₂ ▷η π₁∘ #-}
  π₂[]        : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)}{Θ}{δ : Sub Θ Δ} → π₂ τ [ δ ]t ≡ π₂ (τ ∘ δ)
  {-# REWRITE π₂[] #-} 

p : ∀{Γ C} → Sub (Γ ▷ C) Γ
p = π₁ id
pβ : ∀{Δ Γ C}(σ : Sub Δ Γ)(t : Tm Δ (C [ σ ]T)) → p ∘ ( _,₊_ {C = C} σ t ) ≡ σ
pβ {Δ}{Γ}{C} σ t = sym (π₁∘ {τ = id} )
  -- begin 
  --   p ∘ ( _,₊_ {C = C} σ t ) 
  --   ≡⟨ sym (π₁∘ {τ = id} ) ⟩
  --   π₁ (id ∘ (_,₊_ {C = C} σ t))
  --   ≡⟨ refl ⟩ 
  --   π₁ (_,₊_ {C = C} σ t)
  --   ≡⟨ refl ⟩ 
  --   σ 
  --   ∎
{-# REWRITE pβ #-}

-- For working with de Bruijn index 0
v : ∀{Γ C} → Tm (Γ ▷ C) (C [ p ]T)
v = π₂ id
vβ : ∀{Δ Γ C}(σ : Sub Δ Γ)(t : Tm Δ (C [ σ ]T)) → v [ _,₊_ {C = C} σ t ]t ≡ t
vβ {Δ}{Γ}{C} σ t = refl 
_^_ : ∀{Δ Γ}(σ : Sub Δ Γ)(C : Ty Γ) → Sub (Δ ▷ C [ σ ]T) (Γ ▷ C)
_^_ {Δ}{Γ}(σ)(C) = σ ∘ p ,₊ v
_/v : ∀{Γ C} → Tm Γ C → Sub Γ (Γ ▷ C)
t /v = id ,₊ t
v↦ : ∀{Γ C} → Tm Γ C → Sub Γ (Γ ▷ C)
v↦ {Γ}{C} t = _,₊_ {C = C} id t
v⟨_⟩↦ : ∀{Γ} → (C : Ty Γ) → Tm Γ C → Sub Γ (Γ ▷ C)
v⟨_⟩↦ {Γ} C t = _,₊_ {C = C} id t

-- For working with de Bruijn index 1
pop : ∀{Γ : Con}{C : Ty Γ}{C' : Ty (Γ ▷ C)} → 
  π₁ ( id ∘ π₁ {C = C'} id ) ≡ p ∘ p
pop {Γ}{C}{C'} = π₁∘ {τ = id}{δ = π₁ {C = C'} id}
p1≡ : ∀{Γ : Con}{C : Ty Γ}{C' : Ty (Γ ▷ C)}{s : Tm Γ C}{s' : Tm Γ (C' [ id ,₊ s ]T)} →
  π₁ (p {Γ = (Γ ▷ C)}{C = C'}) ∘ (id ,₊ s ,₊ s') ≡ id
p1≡ {Γ}{C}{C'}{s}{s'} = begin
  π₁ (p {Γ = (Γ ▷ C)}{C = C'}) ∘ (id ,₊ s ,₊ s')
    ≡⟨ sym (π₁∘ {τ = (p {Γ = (Γ ▷ C)}{C = C'})}{δ = (id ,₊ s ,₊ s')} )⟩
  π₁ ((p {Γ = (Γ ▷ C)}{C = C'}) ∘ (id ,₊ s ,₊ s'))
    ≡⟨ refl ⟩
  id
  ∎
{-# REWRITE p1≡ pop #-}
v1≡ : ∀{Γ : Con}{C : Ty Γ}{C' : Ty (Γ ▷ C)}{s : Tm Γ C}{s' : Tm Γ (C' [ id ,₊ s ]T)} →
  (π₂ (p {Γ = (Γ ▷ C)}{C = C'})) [ id ,₊ s ,₊ s' ]t ≡ s
v1≡ {Γ}{C}{C'}{s}{s'} = π₂[] {τ = p {Γ = (Γ ▷ C)}{C = C'}}
{-# REWRITE v1≡ #-}

infixl 5 _▷_
infixl 40 _[_]T
infixl 40 _[_∣_]T
infixl 40 _[id]T _[id]t
infixl 41 v⟨_⟩↦
infixl 5 _,₊_
infixr 8 _∘_
infixl 40 _[_]t
infixl 40 _[_∣_]t