{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module DCwF where

ap : ∀{X : Set}(Y : X → Set){x x' : X} → x ≡ x' → Y(x) → Y(x')
ap Y refl y = y 

open import CwF
open import PCwF
open import NPCwF

postulate
    Hom : ∀{Γ : Con}{C : Ty Γ} → Tm Γ (C ⁻ᵗ) → Tm Γ C → Ty Γ
    Hom[_]≡ : ∀{Δ Γ : Con}(γ : Sub Δ Γ){C : Ty Γ}{t : Tm Γ (C ⁻ᵗ)}{t' : Tm Γ C} →
        (Hom t t') [ γ ]T ≡ Hom (t [ γ ]t) (t' [ γ ]t)
    {-# REWRITE Hom[_]≡ #-}
    rfl : ∀{Γ : Con}{Γn : neutC Γ}{C : Ty Γ}(t : Tm Γ (C ⁻ᵗ)) → Tm Γ (Hom t (-_ {Γn = Γn} t))
    -- rfl[_]≡ : ∀{Δ Γ : Con}{Γn : neutC Γ}{Δn : neutC Δ}(γ : Sub Δ Γ){C : Ty Γ}{t : Tm Γ (C ⁻ᵗ)} → 
    --     (rfl {C = C} t) [ γ ]t ≡ rfl (t [ γ ]t)
    J : ∀{Γ : Con}{Γn : neutC Γ}{C : Ty Γ} → 
            (t : Tm Γ (C ⁻ᵗ)) → 
            (M : Ty (Γ ▷ C ▷ (Hom (t [ p ]t) v))) → 
            Tm Γ (M [ id ,₊ - t ,₊ rfl {Γn = Γn} t ]T) → 
            Tm (Γ ▷ C ▷ (Hom (t [ p ]t) v)) M
    Jβ : ∀{Γ : Con}{Γn : neutC Γ}{C : Ty Γ} → 
            (t : Tm Γ (C ⁻ᵗ)) → 
            (M : Ty (Γ ▷ C ▷ (Hom (t [ p ]t) v))) → 
            (m : Tm Γ (M [ id ,₊ - t ,₊ rfl t ]T)) → 
            (J t M m) [ id ,₊ - t ,₊ rfl {Γn = Γn} t ]t ≡ m

-- Use Id to denote Hom when C is neutral
Id : ∀{Γ : Con}{C : Ty Γ}{Cn : neutT C} → Tm Γ (C ⁻ᵗ) → Tm Γ C → Ty Γ
Id = Hom

-- J whose motive M only depends on t', not on q
J' : ∀{Γ : Con}{Γn : neutC Γ}{C : Ty Γ} → 
            (t : Tm Γ (C ⁻ᵗ)) → 
            (M : Ty (Γ ▷ C )) → 
            Tm Γ (M [ id ,₊ -_ {Γn = Γn} t ]T) → 
            Tm (Γ ▷ C ▷ (Hom (t [ p ]t) v)) (M [ p ]T)
J' t M m = J t (M [ p ]T) m
J'β : ∀{Γ : Con}{Γn : neutC Γ}{C : Ty Γ} → 
            (t : Tm Γ (C ⁻ᵗ)) → 
            (M : Ty (Γ ▷ C )) → 
            (m : Tm Γ (M [ id ,₊ -_ {Γn = Γn} t ]T)) → 
            (J' t M m) [ id ,₊ - t ,₊ rfl {Γn = Γn} t ]t ≡ m
J'β t M m = Jβ t (M [ p ]T) m

-- Symmetry of Id: if C : NeutTy Γ, then for any t : Tm Γ C⁻ and t' : Tm Γ C,
--           Id t t'  →  Id (-t') (-t)
-- since -_[_]≡ isn't a rewrite rule, we have to use some ap's
symm : ∀{Γ : Con}{Γn : neutC Γ}{C : Ty Γ}{Cn : neutT C}{t : Tm Γ (C ⁻ᵗ)}{t' : Tm Γ C} → 
    Tm Γ (Id {Cn = Cn} t t') → Tm Γ (Id {Cn = Cn} (-_ {Γn = Γn} t') (- t))
symm {Γ}{Γn}{C}{Cn}{t}{t'} q = 
    ap (λ x → Tm Γ x) path ((J' t S s) [ id ,₊ t' ,₊ q ]t)
    where
        -- can only formulate this S because we have (Γn ▷neutC Cn) : neutC (Γ ▷ C),
        -- allowing us to form -v : Tm (Γ▷C) (C[p]⁻)
        S : Ty (Γ ▷ C)
        S = Id {Cn = Cn [ p ]neutT} (- v) ((- t) [ p ]t)
        
        lemm1 : t ≡ (- v) [ id ,₊ (- t) ]t
        lemm1 = begin
            t
                ≡⟨ sym (-≡ t) ⟩
            - (- t)
                ≡⟨ refl ⟩
            - ( v [ id ,₊ (- t) ]t )
                ≡⟨ sym (- v [  id ,₊ (- t) ]≡ ) ⟩
            (- v) [ id ,₊ (- t) ]t
            ∎

        s : Tm Γ (S [ v⟨ C ⟩↦ (-_ {Γn = Γn} t) ]T)
        s = ap (λ x → Tm Γ (Id {Cn = Cn} x (-_ {Γn = Γn} t))) lemm1 (rfl t)

        -- S [ p ] [ id ,₊ t' ,₊ q ] ≡ Id (-t') (-t)
        path : S [ p {C = Hom (t [ p ]t) v} ]T [ id ,₊ t' ,₊ q ]T 
             ≡ (Id {Cn = Cn} (- t') (- t))
        path = begin
            S [ p {C = Hom (t [ p ]t) v} ]T [ id ,₊ t' ,₊ q ]T
                ≡⟨ S [ p {C = Hom (t [ p ]t) v} ∣ id ,₊ t' ,₊ q ]T ⟩
            S [ v⟨ C ⟩↦ t' ]T
                ≡⟨ refl ⟩
            Id {Cn = Cn} ((-_ {Γn = Γn ▷neutC Cn} v) [ id ,₊ t' ]t) (- t)
                ≡⟨ cong (λ x →  Id {Cn = Cn} x (-_ {Γn = Γn} t)) (- v [ id ,₊ t' ]≡) ⟩
            Id {Cn = Cn} (- t') (- t)
            ∎