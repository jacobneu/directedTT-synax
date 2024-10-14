{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module NPCwF where

open import CwF
open import PCwF

postulate
    neutC : Con → Prop
    neutT : ∀{Γ : Con} → Ty Γ → Prop
    ◆neutC : neutC ◆
    ⁻neutC : ∀{Γ : Con} → neutC Γ → neutC (Γ ⁻ᶜ)
    ⁻neutT : ∀{Γ : Con}{C : Ty Γ} → neutT C → neutT (C ⁻ᵗ)
    _[_]neutT : ∀{Δ Γ : Con}{C : Ty Γ} → neutT C → (γ : Sub Δ Γ) →  neutT (C [ γ ]T)
    _▷neutC_ : ∀{Γ : Con}{C : Ty Γ} → neutC Γ → neutT C → neutC (Γ ▷ C)

postulate
    ee : ∀ (Γ : Con)(Γn : neutC Γ) → Sub Γ (Γ ⁻ᶜ)
    ee⁻≡ : ∀ (Γ : Con)(Γn : neutC Γ) → (ee Γ Γn) ⁻ˢ ≡ ee (Γ ⁻ᶜ) (⁻neutC Γn)
    eeβ : ∀ (Γ : Con)(Γn : neutC Γ) → (ee Γ Γn) ⁻ˢ ∘ ee Γ Γn ≡ id
    eeη : ∀ (Γ : Con)(Γn : neutC Γ) → ee Γ Γn ∘ (ee Γ Γn) ⁻ˢ ≡ id
    ee∘ : ∀ {Δ Γ : Con}{Δn : neutC Δ}{Γn : neutC Γ}(γ : Sub Δ Γ) → 
            (ee Γ Γn) ⁻ˢ ∘ γ ⁻ˢ ∘ ee Δ Δn ≡ γ
    {-# REWRITE ee⁻≡ eeβ eeη #-}

eeη' : ∀ (Γ : Con)(Γn : neutC Γ) → ee Γ Γn ∘ (ee (Γ ⁻ᶜ) (⁻neutC Γn)) ≡ id
eeη' Γ Γn = begin 
    ee Γ Γn ∘ (ee (Γ ⁻ᶜ) (⁻neutC Γn)) 
    ≡⟨ cong (λ x → ee Γ Γn ∘ x) (sym (ee⁻≡ Γ Γn)) ⟩ 
    ee Γ Γn ∘ (ee Γ Γn) ⁻ˢ
    ≡⟨ eeη Γ Γn ⟩ 
    id 
    ∎
{-# REWRITE eeη' #-}

postulate
    -_ : ∀ {Γ : Con}{Γn : neutC Γ}{C : Ty Γ} → Tm Γ C → Tm Γ (C ⁻ᵗ)
    -≡ : ∀ {Γ : Con}{Γn : neutC Γ}{C : Ty Γ}(t : Tm Γ C) → -_ {Γn = Γn} ( -_ {Γn = Γn} t) ≡ t
    -_[_]≡ : ∀ {Δ Γ : Con}{Δn : neutC Δ}{Γn : neutC Γ}{C : Ty Γ}(t : Tm Γ C)(γ : Sub Δ Γ) → 
            ((-_ {Γn = Γn} t)[ γ ]t) ≡ -_ {Γn = Δn} (t [ γ ]t)
    {-# REWRITE -≡ #-}
    ee▷_ : ∀ {Γ : Con}{Γn : neutC Γ}(A : Ty⁻ Γ) → Sub (Γ ▷ A [ ee Γ Γn ]T) (Γ ▷⁻ A)
    ee▷_-inv : ∀ {Γ : Con}{Γn : neutC Γ}(A : Ty⁻ Γ) → Sub (Γ ▷⁻ A) (Γ ▷ A [ ee Γ Γn ]T)
    ee▷_-β : ∀ {Γ : Con}{Γn : neutC Γ}(A : Ty⁻ Γ) → (ee▷_-inv {Γ = Γ}{Γn = Γn} A) ∘ ee▷ A ≡ id
    ee▷_-η : ∀ {Γ : Con}{Γn : neutC Γ}(A : Ty⁻ Γ) → ee▷ A ∘ (ee▷_-inv {Γ = Γ}{Γn = Γn} A) ≡ id
    π₁ee▷_≡ : ∀ {Γ : Con}{Γn : neutC Γ}(A : Ty⁻ Γ) → 
        π₁ {Γ = Γ ⁻ᶜ} {C = A ⁻ᵗ}((ee▷_ {Γ = Γ}{Γn = Γn} A) ⁻ˢ) ≡ p ⁻ˢ
    {-# REWRITE ee▷_-β ee▷_-η π₁ee▷_≡ #-}
    -- ee▷_[_∣_] :  ∀ {Δ Γ : Con}{Γn : neutC Γ}{Δn : neutC Δ}{Δn⁻ : neutC (Δ ⁻ᶜ)}(A : Ty⁻ Γ)(γ : Sub Δ Γ)(a : Tm Δ (A [ ee Γ Γn ∘ γ ]T)) → 
    --     (ee▷ A) ∘ (γ ,₊ a) ≡ _,₋_ {A = A} γ (-_ {Γn = Δn⁻} (_[_]t⁻ {A = A ⁻ᵗ [ ee Γ Γn ∘ γ ]T} a (ee Δ Δn) ))
    ee▷_[id∣_] :  ∀ {Γ : Con}{Γn : neutC Γ}(A : Ty⁻ Γ)(a : Tm Γ (A [ ee Γ Γn ]T)) → 
        (ee▷ A) ∘ (id ,₊ a) ≡ _,₋_ {A = A} id (-_ {Γn = ⁻neutC Γn} (_[_]t⁻ {A = A ⁻ᵗ [ ee Γ Γn ]T} a (ee Γ Γn) ))
    {-# REWRITE ee▷_[id∣_] #-}

neg-lemma : ∀{Γ : Con}{Γn : neutC Γ}{C : Ty Γ}{t u : Tm Γ C} → 
    (-_ {Γn = Γn} t) ≡ (-_ {Γn = Γn} u) → t ≡ u
neg-lemma {Γ}{Γn}{C}{t}{u} = cong (-_ {Γn = Γn}) {x = - t} {y = - u}
