open import Data.Unit
open import Data.Product
open import Function

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

module IDesc.AdjointFold where

record AdjointScheme {I : Set}{X : I → Set}(F : func I I) : Set₁ where

  field
    L : func I I
    R : func I I
    η : ∀ {X} → X ⇒ ⟦ R ◎ L ⟧func X
    ε : ∀ {X} → ⟦ L ◎ R ⟧func X ⇒ X

--   G : (I → Set) → (I → Set)
--   G x = ⟦ L ⟧func (⟦ F ⟧func (⟦ R ⟧func x))

  G : func I I
  G = L ◎ F ◎ R

  σ : ∀ {X} → ⟦ L ◎ F ⟧func X ⇒ ⟦ G ◎ L ⟧func X
  σ {X} {i = i} = ◎-assoc' {F = L ◎ F} {G = R} {H = L} ∘ ◎-⟦⟧-distrib' {F = L ◎ F} {G = R ◎ L} ∘ ⟦ L ◎ F ⟧fmap η

  G' : func I I
  G' = R ◎ F ◎ L

  τ : ∀ {X} → ⟦ G' ◎ R ⟧func X ⇒ ⟦ R ◎ F ⟧func X
  τ = ⟦ R ◎ F ⟧fmap ε ∘ ◎-⟦⟧-distrib'' {F = R ◎ F} {G = L ◎ R} ∘ ◎-assoc'' {F = R ◎ F} {G = L} {H = R}

  {-# NON_TERMINATING #-}
  ⊣-fold : (⟦ G ⟧func X ⇒ X) → ⟦ L ⟧func (μ F) ⇒ X
  ⊣-fold a = a ∘ ⟦ G ⟧fmap (⊣-fold a) ∘ ◎-⟦⟧-distrib'' {F = G} ∘ σ ∘ ◎-⟦⟧-distrib' {F = L} ∘ ⟦ L ⟧fmap (inᵒ F)

open AdjointScheme

×→ : ∀ {X}(A : Set)(F : func ⊤ ⊤)  → AdjointScheme {⊤} {X} F
×→ A F = record { L = mk λ _ → `Σ A λ _ → `var tt
                ; R = mk λ _ → `Π A λ _ → `var tt
                ; η = flip _,_
                ; ε = uncurry (flip _$_)}

para : ∀ {A F X} → (⟦ G {X = X} (×→ A F) ⟧func X ⇒ X) → ⟦ L {X = X} (×→ A F) ⟧func (μ F) tt → X tt
para {A} {F} a = ⊣-fold (×→ A F) a
