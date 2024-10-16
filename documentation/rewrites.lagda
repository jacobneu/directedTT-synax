\documentclass[11pt]{article}

\title{Rewrite rules for directed type theory}
\author{Jacob Neumann}
\usepackage{agda}
\begin{document}

\begin{itemize}
\begin{code}[hide]
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module rewrites where

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
\end{code}
\item Category laws:
\begin{code}
postulate
  idl         : ∀{Γ Δ}(γ : Sub Δ Γ) → id ∘ γ ≡ γ
  idr         : ∀{Γ Δ}(γ : Sub Δ Γ) → γ ∘ id ≡ γ
\end{code}
\begin{code}[hide]
  {-# REWRITE ass idl idr #-}
postulate 
  -- terminal object
  ◆           : Con
  ε           : ∀{Γ} → Sub Γ ◆
  ◆η          : ∀{Γ}(σ : Sub Γ ◆) → σ ≡ ε
  
  -- a family structure
  _[_]T       : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ
\end{code}
\begin{code}
postulate
  _[_∣_]T     : ∀{Θ Δ Γ}(C : Ty Γ)(γ : Sub Δ Γ)(δ : Sub Θ Δ) →
                C [ γ ]T [ δ ]T ≡ C [ γ ∘ δ ]T
  _[id]T      : ∀{Γ}(C : Ty Γ) → C [ id ]T ≡ C
\end{code}
\begin{code}[hide]
{-# REWRITE _[_∣_]T _[id]T #-}
postulate
  _[_]t       : ∀{Δ Γ}{C : Ty Γ} → Tm Γ C → (γ : Sub Δ Γ) → Tm Δ (C [ γ ]T)
\end{code}
\item Family structure:
\begin{code}
postulate
  _[_∣_]t     : c [ γ ]t [ δ ]t ≡ c [ γ ∘ δ ]t
  _[id]t      : c [ id ]t ≡ c
\end{code}
\begin{code}[hide]
  {-# REWRITE _[_∣_]t _[id]t #-}

  -- extend a Con with a Ty
  _▷_         : (Γ : Con) → Ty Γ → Con
  _,₊_        : ∀{Δ Γ C}(σ : Sub Δ Γ) → Tm Δ (C [ σ ]T) → Sub Δ (Γ ▷ C)
  π₁          : ∀{Δ Γ C}(τ : Sub Δ (Γ ▷ C)) → Sub Δ Γ
  π₂          : ∀{Δ Γ C}(τ : Sub Δ (Γ ▷ C)) → Tm Δ (C [ π₁ τ ]T)
\end{code}
\item (Positive) Context extension 
\begin{code}
postulate
  ▷β₁         : ∀{Δ Γ C}{σ : Sub Δ Γ}{t : Tm Δ (C [ σ ]T)} → 
                π₁ (_,₊_ {C = C} σ t) ≡ σ
\end{code}
\begin{code}[hide]
  {-# REWRITE ▷β₁ #-}
\end{code}
\begin{code}
postulate
  ▷β₂         : ∀{Δ Γ C}{σ : Sub Δ Γ}{t : Tm Δ (C [ σ ]T)} → 
                π₂ (_,₊_ {C = C} σ t) ≡ t
  ▷η          : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)} → π₁ τ ,₊ π₂ τ ≡ τ
  π₁∘         : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)}{Θ}{δ : Sub Θ Δ} → 
                π₁ (τ ∘ δ) ≡ π₁ τ ∘ δ
\end{code}
\begin{code}[hide]
  {-# REWRITE ▷β₂ ▷η π₁∘ #-}
\end{code}
\begin{code}
postulate
  π₂[]        : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)}{Θ}{δ : Sub Θ Δ} → 
                π₂ τ [ δ ]t ≡ π₂ (τ ∘ δ)
\end{code}
\begin{code}[hide]
  {-# REWRITE π₂[] #-} 
              

infixl 5 _▷_
infixl 40 _[_]T
infixl 40 _[_∣_]T
infixl 40 _[id]T _[id]t
infixl 5 _,₊_
infixr 8 _∘_
infixl 40 _[_]t
infixl 40 _[_∣_]t


infix 45 _⁻ᶜ _⁻ˢ _⁻ᵗ

postulate
  _⁻ᶜ : Con → Con
  _⁻ˢ : ∀{Δ Γ : Con} → Sub Δ Γ → Sub (Δ ⁻ᶜ) (Γ ⁻ᶜ)
  _⁻ᵗ : ∀{Γ} → Ty Γ → Ty Γ

-- variable
--   A B : Ty (Γ ⁻ᶜ)
\end{code}
\item Negation
\begin{code}
postulate
  ◆⁻≡         : ◆ ⁻ᶜ ≡ ◆
  invC        : ∀{Γ} → (Γ ⁻ᶜ) ⁻ᶜ ≡ Γ
\end{code}
\begin{code}[hide]
  {-# REWRITE ◆⁻≡ invC #-}
\end{code}
\begin{code}
postulate
  invS        : ∀{Δ Γ}{σ : Sub Δ Γ} → (σ ⁻ˢ) ⁻ˢ ≡ σ
  invT        : ∀{Γ}{C : Ty Γ} → (C ⁻ᵗ ) ⁻ᵗ ≡ C
\end{code}
\begin{code}[hide]
  {-# REWRITE invS invT #-}
\end{code}
\begin{code}
postulate
  id⁻≡        : ∀{Γ} →  (id {Γ = Γ}) ⁻ˢ ≡ id
  _∘⁻≡_       : ∀{Θ Δ Γ}(γ : Sub Δ Γ)(δ : Sub Θ Δ) → 
                (γ ∘ δ) ⁻ˢ ≡ (γ ⁻ˢ) ∘ (δ ⁻ˢ)
  nat⁻        : ∀{Δ Γ C}(γ : Sub Δ Γ) → (C [ γ ]T) ⁻ᵗ ≡ (C ⁻ᵗ) [ γ ]T
\end{code}
\begin{code}[hide]
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

infixl 5 _▷⁻_
infixl 40 _[_]T⁻
infixl 40 _[_∣_]T⁻
infixl 40 _[id]T⁻ _[id]t⁻
-- infixl 41 v₋⟨_⟩↦
infixl 5 _,₋_
infixl 40 _[_]t⁻
infixl 40 _[_∣_]t⁻
\end{code}
\end{itemize}

\end{document}
