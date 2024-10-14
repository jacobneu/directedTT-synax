{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module 00-categories where

open import CwF
open import PCwF
open import NPCwF
open import DCwF
open import 1-1-DCwF

variable
    Γn : neutC Γ

COMP : (t : Tm Γ (C ⁻ᵗ)) → Ty (Γ ▷ C)
COMP t = Hom (t [ p ]t) v
COMP' : (t : Tm Γ (C ⁻ᵗ)) → Ty (Γ ▷ C)
COMP' t = (COMP t) ⁻ᵗ

lemm : (t : Tm Γ (C ⁻ᵗ)) → 
    (COMP' {C = C} t) [ p {C = Hom (t [ p ]t) v} ]T ≡ Hom (t [ p ∘ p ]t) (v [ p ]t) ⁻ᵗ
lemm {Γ}{C} t = sym (nat⁻ {C = COMP t} (p {C = Hom (t [ p ]t) v}))
lemm2 : (t : Tm Γ (C ⁻ᵗ)) → (t' : Tm Γ C) →
    (Hom t t') ⁻ᵗ ≡ (COMP' {C = C} t) [ id ,₊ t' ]T
lemm2 {Γ}{C} t t' = nat⁻ {C = COMP t} (id ,₊ t')
    -- begin
    -- (COMP {C = C} t) ⁻ᵗ [ id ,₊ t' ]T
    --     ≡⟨ sym (nat⁻ {C = COMP t} (id ,₊ t')) ⟩
    -- (COMP {C = C} t [ id ,₊ t' ]T) ⁻ᵗ
    --     ≡⟨ refl ⟩
    -- (Hom t t') ⁻ᵗ
    -- ∎   
    -- begin
    -- (COMP {C = C} t) ⁻ᵗ [ p {C = Hom (t [ p ]t) v} ]T
    --     ≡⟨ sym (nat⁻ {C = COMP t} (p {C = Hom (t [ p ]t) v})) ⟩
    -- ((COMP {C = C} t) [ p {C = Hom (t [ p ]t) v} ]T) ⁻ᵗ 
    --     ≡⟨ refl ⟩
    -- Hom (t [ p ∘ p ]t) (v [ p ]t) ⁻ᵗ
    -- ∎

_·_ : ∀{t t' : Tm Γ (C ⁻ᵗ)}{t'' : Tm Γ C} → 
    Tm Γ (Hom t (-_ {Γn = Γn} t')) → Tm Γ (Hom t' t'') → Tm Γ (Hom t t'')
_·_ {Γ}{C}{Γn}{t}{t'}{t''} f g = (J' t' (COMP t) f) [ id ,₊ t'' ,₊ g ]t

-- _·⁻_ : ∀{t t' : Tm Γ (C ⁻ᵗ)}{t'' : Tm Γ C} → 
--     Tm Γ (Hom t (-_ {Γn = Γn} t')) → Tm Γ (Hom t' t'') → Tm Γ (Hom t t'' ⁻ᵗ)
-- _·⁻_ {Γ}{C}{Γn}{t}{t'}{t''} f g = {! (J' t' (Hom (t [ p ]t) v ⁻ᵗ) ?) [ id ,₊ t'' ,₊ g ]t  !}

l-unit : ∀{t t' : Tm Γ (C ⁻ᵗ)}(f : Tm Γ (Hom t (-_ {Γn = Γn} t'))) → 
    Tm Γ (Id {Cn = Homn} (-_ {Γn = Γn} (f · (rfl t'))) f)
l-unit {Γ}{C}{Γn}{t}{t'} f = 
    ap  (λ f' → Tm Γ (Id {Cn = Homn} f' f)) 
        (cong -_ (sym (J'β t' (COMP t) f)))  --  : -f ≡ -(f · rfl) 
        (rfl {Γn = Γn} (- f))                --  : Tm Γ (Id -f f)

-- r-unit : ∀{t' : Tm Γ (C ⁻ᵗ)}{t'' : Tm Γ C}(g : Tm Γ (Hom t' t'')) → 
--     Tm Γ (Id {Cn = Homn} (-_ {Γn = Γn} (_·_ {Γn = Γn} (rfl t') g)) g)
-- r-unit {Γ}{C}{Γn}{t'}{t''} g = ap (Tm Γ) lemm4 ((J t' R r₀) [ id ,₊ t'' ,₊ g ]t)
--     where
--         rfl·⁻ : Tm (Γ ▷ C ▷ Hom (t' [ p ]t) v) ((Hom (t' [ p ]t) v [ p ]T) ⁻ᵗ)
--         rfl·⁻ = (ap (Tm  (Γ ▷ C ▷ Hom (t' [ p ]t) v)) (lemm {C = C} t') (J' {Γn = Γn}{C = C} t' (COMP' t') (ap (Tm Γ) (lemm2 t' (- t')) (-_ {Γn = Γn} (rfl t')))))
        
--         rfl·⁻[] : rfl·⁻ [ id ,₊ - t' ,₊ rfl t' ]t ≡ - (rfl t')
--         rfl·⁻[] = ?  

--         R : Ty (Γ ▷ C ▷ Hom (t' [ p ]t) v)
--         R = Id {Cn = Homn} rfl·⁻ v

--         lemm3 : Id {Cn = Homn} (-_ {Γn = Γn} (rfl {Γn = Γn} t')) (rfl {C = C} t') 
--                 ≡ R [ id ,₊ - t' ,₊ rfl {Γn = Γn} t' ]T
--         lemm3 = sym (begin
--             R [ id ,₊ - t' ,₊ rfl {Γn = Γn} t' ]T 
--                 ≡⟨ {!  refl !} ⟩
--             Id {Cn = Homn} {!   !} (rfl {Γn = Γn}{C = C} t')
--                 ≡⟨ {!   !} ⟩
--             Id {Cn = Homn} (-_ {Γn = Γn} (rfl {Γn = Γn} t')) (rfl {C = C} t')
--             ∎)

--         r₀ : Tm Γ (R [ id ,₊ - t' ,₊ rfl {Γn = Γn} t' ]T)
--         r₀ = ap (Tm Γ) lemm3 (rfl {Γn = Γn} (- rfl t'))

--         lemm4 : R [ id ,₊ t'' ,₊ g ]T ≡ Id {Cn = Homn} (-_ {Γn = Γn} (_·_ {Γn = Γn} (rfl t') g)) g
--         lemm4 = {!   !}