open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Function

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.FinalCoalgebra


module IDesc.AdjointFold where

record AdjointScheme {I : Set}{X : I → Set}(F : func I I) : Set₁ where

  field
    L : func I I
    R : func I I
    η : ∀ {X} → X ⇒ ⟦ R ◎ L ⟧func X
    ε : ∀ {X} → ⟦ L ◎ R ⟧func X ⇒ X

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

  {-# NON_TERMINATING #-}
  ⊣-unfold : (X ⇒ ⟦ G' ⟧func X) → X ⇒ ⟦ R ⟧func (ν F)
  ⊣-unfold c = ⟦ R ⟧fmap (outᵒ F) ∘ ◎-⟦⟧-distrib'' {F = R} ∘ τ ∘ ◎-⟦⟧-distrib' {F = G'} ∘ ⟦ G' ⟧fmap (⊣-unfold c) ∘ c

open AdjointScheme

×→ : ∀ {X}(A : Set)(F : func ⊤ ⊤)  → AdjointScheme {⊤} {X} F
×→ A F = record { L = mk λ _ → `Σ A λ _ → `var tt
                ; R = mk λ _ → `Π A λ _ → `var tt
                ; η = flip _,_
                ; ε = uncurry (flip _$_)}

para : ∀ {A F X} → (⟦ G {X = X} (×→ A F) ⟧func X ⇒ X) → ⟦ L {X = X} (×→ A F) ⟧func (μ F) tt → X tt
para {A} {F} a = ⊣-fold (×→ A F) a

+△ : ∀ {X}(F : func ⊤ ⊤) → AdjointScheme {⊤} {X} F
+△ F = record { L = mk λ _ → `σ 2 λ { zero → `var tt ; (suc zero) → `var tt ; (suc (suc ())) }
              ; R = mk λ _ → `var tt `× `var tt
              ; η = < (λ x → zero , x) , (λ x → (suc zero) , x) >
              ; ε = λ { (zero , xy) → proj₁ xy ; (suc zero , xy) → proj₂ xy ; (suc (suc ()) , _) } }

apo : ∀ {F X} → (X ⇒ ⟦ G' {X = X} (+△ F) ⟧func X) → X tt → ⟦ R {X = X} (+△ F) ⟧func (ν F) tt
apo {F} c = ⊣-unfold (+△ F) c
