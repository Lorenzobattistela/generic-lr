{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Specific.Syntax
  (Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Relation.Binary.PropositionalEquality

  open Ident 0# 1#

  private
    variable
      π ρ : Ann
      s t : LTree
      P Q R : Vector Ann _

  infix 4 _⊴*_ _⊴ᴹ_
  infixr 6 _+*_
  infixr 7 _*ₗ_

  _⊴*_ = Lift₂ _⊴_
  _⊴ᴹ_ = Lift₂ᴹ _⊴_
  0* = lift₀ 0#
  _+*_ = lift₂ _+_
  _*ₗ_ : Ann → Vector Ann s → Vector Ann s
  ρ *ₗ R = lift₁ (ρ *_) R

  data Ty : Set where
    tι : Ty
    [_·_]⊸_ : (ρ : Ann) (S T : Ty) → Ty

  private
    variable
      A B C : Ty

  open import Generic.Linear.Syntax Ty Ann
  open Ctx public renaming (s to shape; R to use-ctx; Γ to ty-ctx)

  data Tm (RΓ : Ctx) : Ty → Set where
    var : let ctx R Γ = RΓ in
          (i : Ptr _) (sp : R ⊴* (1ᴹ i)) (q : Γ i ≡ A) → Tm RΓ A
    app : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) ([ ρ · A ]⊸ B)) (N : Tm (ctx Q Γ) A)
          (sp : R ⊴* P +* ρ *ₗ Q) → Tm RΓ B
    lam : (M : Tm (RΓ ++ᶜ [ ρ · A ]ᶜ) B) → Tm RΓ ([ ρ · A ]⊸ B)