{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality 

module polarDependent where

open import CwF 
open import PCwF

variable
    A : Ty⁻ Γ

postulate
    Π : (A : Ty⁻ Γ) → Ty (Γ ▹⁻ A) → Ty Γ
    lam : ∀{A : Ty⁻ Γ}{P : Ty (Γ ▹⁻ A)} → Tm (Γ ▹⁻ A) P → Tm Γ (Π A P)
    app : ∀{A : Ty⁻ Γ}{P : Ty (Γ ▹⁻ A)} → Tm Γ (Π A P) → Tm (Γ ▹⁻ A) P
    Πβ : ∀{A : Ty⁻ Γ}{P : Ty (Γ ▹⁻ A)} → (e : Tm (Γ ▹⁻ A) P) → app {Γ = Γ}{A = A}(lam e) ≡ e
    Πη : ∀{A : Ty⁻ Γ}{P : Ty (Γ ▹⁻ A)} → (f : Tm Γ (Π A P)) → lam(app f) ≡ f
    Π[_]≡ : ∀{Δ Γ : Con}{γ : Sub Δ Γ}{A : Ty⁻ Γ}{P : Ty (Γ ▹⁻ A)} → 
        (Π A P) [ γ ]T ≡ Π (A [ γ ]T⁻) (P [ γ ^⁻ A ]T)
    {-# REWRITE Πβ Πη Π[_]≡ #-}
    lam[_]≡ : ∀{Δ Γ : Con}{γ : Sub Δ Γ}{A : Ty⁻ Γ}{P : Ty (Γ ▹⁻ A)}(e : Tm (Γ ▹⁻ A) P) →
        (lam {A = A} e) [ γ ]t ≡ lam (e [ γ ^⁻ A ]t)
    app[_]≡ : ∀{Δ Γ : Con}{γ : Sub Δ Γ}{A : Ty⁻ Γ}{P : Ty (Γ ▹⁻ A)}(f : Tm Γ (Π A P)) →
        (app f) [ γ ^⁻ A ]t ≡ app (f [ γ ]t)
    {-# REWRITE lam[_]≡ app[_]≡ #-}

_$_ : ∀{A : Ty⁻ Γ}{P : Ty (Γ ▹⁻ A)} → (Tm Γ (Π A P)) → (a : Tm⁻ Γ A) → Tm Γ (P [ v₋⟨ A ⟩↦ a ]T)
_$_ {Γ}{A} f a = (app f) [ v₋⟨ A ⟩↦ a ]t

_⟶_ : Ty⁻ Γ → Ty Γ → Ty Γ
A ⟶ C = Π A (C [ p₋ {A = A} ]T) 

     