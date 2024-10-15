
\begin{itemize}
\item Category laws:
\begin{code}
  ass         : ∀{Ξ Δ Γ Θ} → (ϑ : Sub Ξ Θ)(δ : Sub Θ Δ)(γ : Sub Δ Γ) →
                (γ ∘ δ) ∘ ϑ ≡ γ ∘ (δ ∘ ϑ)
  idl         : ∀{Γ Δ}(γ : Sub Δ Γ) → id ∘ γ ≡ γ
  idr         : ∀{Γ Δ}(γ : Sub Δ Γ) → γ ∘ id ≡ γ
\end{code}

\item Family structure:
\begin{code}
  _[_∣_]T     : ∀{Θ Δ Γ}(C : Ty Γ)(γ : Sub Δ Γ)(δ : Sub Θ Δ) →
                C [ γ ]T [ δ ]T ≡ C [ γ ∘ δ ]T
  _[id]T      : ∀{Γ}(C : Ty Γ) → C [ id ]T ≡ C
  _[_∣_]t     : c [ γ ]t [ δ ]t ≡ c [ γ ∘ δ ]t
  _[id]t      : c [ id ]t ≡ c
\end{code}

\item (Positive) Context extension:
\begin{code}
  ▷β₁         : ∀{Δ Γ C}{σ : Sub Δ Γ}{t : Tm Δ (C [ σ ]T)} → π₁ (σ ,₊ t) ≡ σ
  ▷β₂         : ∀{Δ Γ C}{σ : Sub Δ Γ}{t : Tm Δ (C [ σ ]T)} → π₂ (σ ,₊ t) ≡ t
  ▷η          : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)} → π₁ τ ,₊ π₂ τ ≡ τ
  π₁∘         : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)}{Θ}{δ : Sub Θ Δ} → π₁ (τ ∘ δ) ≡ π₁ τ ∘ δ
  π₂[]        : ∀{Δ Γ C}{τ : Sub Δ (Γ ▷ C)}{Θ}{δ : Sub Θ Δ} → π₂ τ [ δ ]t ≡ π₂ (τ ∘ δ)
\end{code}

\item Negation:
\begin{code}
  ◆⁻≡ : ◆ ⁻ᶜ ≡ ◆
  invC : ∀{Γ} → (Γ ⁻ᶜ) ⁻ᶜ ≡ Γ
  invS : ∀{Δ Γ}{σ : Sub Δ Γ} → (σ ⁻ˢ) ⁻ˢ ≡ σ
  invT : ∀{Γ}{C : Ty Γ} → (C ⁻ᵗ ) ⁻ᵗ ≡ C
  id⁻≡ : ∀{Γ} →  (id {Γ = Γ}) ⁻ˢ ≡ id
  _∘⁻≡_ : ∀{Θ Δ Γ}(γ : Sub Δ Γ)(δ : Sub Θ Δ) → (γ ∘ δ) ⁻ˢ ≡ (γ ⁻ˢ) ∘ (δ ⁻ˢ)
  nat⁻ : ∀{Δ Γ C}(γ : Sub Δ Γ) → (C [ γ ]T) ⁻ᵗ ≡ (C ⁻ᵗ) [ γ ]T
\end{code}


\end{itemize}