{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
import Algebra.Definitions as Defs
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Reflexive; Transitive)

module Specific.Syntax.Renaming
  (Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  (⊴-refl : Reflexive _⊴_) (⊴-trans : Transitive _⊴_)
  (open Defs _⊴_) (let module ⊵ = Defs (flip _⊴_))
  (+-mono : Congruent₂ _+_) (*-mono : Congruent₂ _*_)
  (+-identity-⊴ : Identity 0# _+_) (+-identity-⊵ : ⊵.Identity 0# _+_)
  (+-interchange : Interchangable _+_ _+_)
  (1-* : ∀ x → (1# * x) ⊴ x) (*-1 : ∀ x → x ⊴ (x * 1#)) (*-* : Associative _*_)
  (0-* : ∀ x → (0# * x) ⊴ 0#) (*-0 : ∀ x → 0# ⊴ (x * 0#))
  (+-* : ∀ x y z → ((x + y) * z) ⊴ ((x * z) + (y * z)))
  (*-+ : ∀ x y z → ((x * y) + (x * z)) ⊴ (x * (y + z)))
  where

  open import Specific.Syntax Ann _⊴_ 0# _+_ 1# _*_
  open import Specific.Syntax.Prelude Ann _⊴_ 0# _+_ 1# _*_
    ⊴-refl ⊴-trans +-mono *-mono +-identity-⊴ +-identity-⊵ +-interchange
    1-* *-1 *-* 0-* *-0 +-* *-+
  open import Specific.Syntax.Traversal Ann _⊴_ 0# _+_ 1# _*_
    ⊴-refl ⊴-trans +-mono *-mono +-identity-⊴ +-identity-⊵ +-interchange
    1-* *-1 *-* 0-* *-0 +-* *-+
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  private
    variable
      A B C : Ty
      PΓ QΔ RΘ : Ctx

  record Ren (PΓ QΔ : Ctx) : Set where
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
      t = QΔ .shape ; Q = QΔ .use-ctx ; Δ = QΔ .ty-ctx
    field
      act : Ptr t → Ptr s
      use-pres : P ⊴* unrow (row Q *ᴹ λ j i → 1ᴹ (act j) i)
      ty-pres : ∀ j → Γ (act j) ≡ Δ j
  open Ren public

  LVar-kit : Kit LVar
  LVar-kit .psh PQ v .idx = v .idx
  LVar-kit .psh PQ v .basis = ⊴*-trans PQ (v .basis)
  LVar-kit .psh PQ v .ty-eq = v .ty-eq
  LVar-kit .vr = id
  LVar-kit .tm = var
  LVar-kit .wk v .idx = ↙ (v .idx)
  LVar-kit .wk v .basis = v .basis ++₂ ⊴*-refl
  LVar-kit .wk v .ty-eq = v .ty-eq

  ren : Ren PΓ QΔ → Tm QΔ A → Tm PΓ A
  ren r = trav LVar-kit
    (record { matrix = 1ᴹ ∘ r .act
            ; act = λ j → lvar (r .act j) ⊴*-refl (r .ty-pres j)
            ; use-pres = r .use-pres
            })
