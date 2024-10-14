{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module 1-1-DCwF where


open import CwF
open import PCwF
open import NPCwF
open import DCwF

postulate
    Homn : ∀{Γ : Con}{C : Ty Γ}{t : Tm Γ (C ⁻ᵗ)}{t' : Tm Γ C} → neutT (Hom t t')
    UIP¹ : ∀{Γ : Con}{C : Ty Γ}{t : Tm Γ (C ⁻ᵗ)}{t' : Tm Γ C} → 
            {p : Tm Γ ((Hom t t') ⁻ᵗ)}{q : Tm Γ (Hom t t')} →  
            (α : Tm Γ ((Id {Cn = Homn} p q) ⁻ᵗ)) → (β : Tm Γ (Id {Cn = Homn} p q)) → 
            Tm Γ (Id {Cn = Homn} α β)