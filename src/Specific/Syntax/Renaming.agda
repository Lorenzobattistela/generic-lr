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
  open import Generic.Linear.Syntax Ty Ann

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Vector.Properties
  open import Data.LTree.Matrix
  open import Data.LTree.Matrix.Properties
  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  open Ident 0# 1#
  open Mult 0# _+_ _*_
  open Mult-cong 0# _+_ _*_ _⊴_ _⊴_ _⊴_ ⊴-refl +-mono *-mono
  open Plus-cong _+_ _⊴_ _⊴_ _⊴_ +-mono
  open IdentMult 0# 1# _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono +-identity-⊴ 1-* 0-*
  open MultIdent 0# 1# (flip _⊴_) 0# _+_ _*_ ⊴-refl (flip ⊴-trans)
    +-mono +-identity-⊵ *-1 *-0
  open PlusMult _+_ _⊴_ 0# _+_ _*_ ⊴-refl ⊴-trans
    +-mono (+-identity-⊵ .proj₂ 0#) +-interchange +-*
  open LeftScaleMult _⊴_ 0# _+_ 0# _+_ _*_ _*_ _*_ _*_ ⊴-refl ⊴-trans
    +-mono *-0 *-+ *-*
  open SumCong _⊴_ 0# _+_ ⊴-refl +-mono
  open Sum0 (flip _⊴_) 0# _+_ (flip ⊴-trans)
    ⊴-refl +-mono (+-identity-⊵ .proj₂ 0#)

  ⊴*-refl : ∀ {s} → Reflexive (_⊴*_ {s = s})
  ⊴*-refl .get i = ⊴-refl
  ⊴*-trans : ∀ {s} → Transitive (_⊴*_ {s = s})
  ⊴*-trans PQ QR .get i = ⊴-trans (PQ .get i) (QR .get i)

  ⊴ᴹ-refl : ∀ {s t} → Reflexive (_⊴ᴹ_ {s = s} {t})
  ⊴ᴹ-refl .get i j = ⊴-refl
  ⊴ᴹ-trans : ∀ {s t} → Transitive (_⊴ᴹ_ {s = s} {t})
  ⊴ᴹ-trans MN NO .get i j = ⊴-trans (MN .get i j) (NO .get i j)

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

  bindRen : Ren PΓ QΔ → Ren (PΓ ++ᶜ RΘ) (QΔ ++ᶜ RΘ)
  bindRen r .act (↙ j) = ↙ (r .act j)
  bindRen r .act (↘ j) = ↘ j
  bindRen {PΓ = ctx {s} P Γ} {RΘ = ctx {t} R Θ} r .use-pres .get (↙ i) =
    ⊴-trans (r .use-pres .get i)
            (⊴-trans (+-identity-⊵ .proj₂ _)
                     (+-mono ⊴-refl
                             (⊴-trans (∑-0 t)
                                      (∑-cong {t} (mk λ j → *-0 _)))))
  bindRen {QΔ = ctx {s} Q Δ} {RΘ = ctx {t} R Θ} r .use-pres .get (↘ i) =
    ⊴-trans (*ᴹ-1ᴹ (row R) .get here i)
            (⊴-trans (+-identity-⊵ .proj₁ _)
                     (+-mono (⊴-trans (∑-0 s)
                                      (∑-cong {s} (mk λ j → *-0 _)))
                             ⊴-refl))
  bindRen r .ty-pres (↙ j) = r .ty-pres j
  bindRen r .ty-pres (↘ j) = refl

  ren : Ren PΓ QΔ → Tm QΔ A → Tm PΓ A
  ren r (var j sp refl) = var
    (r .act j)
    (⊴*-trans (r .use-pres)
              (⊴*-trans (unrowL₂ (*ᴹ-cong (rowL₂ sp) (mk λ j i → ⊴-refl {1ᴹ (r .act j) i})))
                        (mk λ i → 1ᴹ-*ᴹ (λ j i → 1ᴹ (r .act j) i) .get j i)))
    (r .ty-pres j)
  ren {PΓ = ctx {s} Rs Γ} {ctx {t} Rt Δ} r (app {P = Pt} {Q = Qt} M N sp) =
    app (ren (record { Ren r; use-pres = ⊴*-refl }) M)
        (ren (record { Ren r; use-pres = ⊴*-refl }) N)
        (⊴*-trans (r .use-pres)
                  (unrowL₂ (⊴ᴹ-trans (*ᴹ-cong (rowL₂ sp) ⊴ᴹ-refl)
                                     (⊴ᴹ-trans (+ᴹ-*ᴹ {t = t} _ _ _)
                                               (+ᴹ-cong ⊴ᴹ-refl (*ₗ-*ᴹ {t = t} _ _ _))))))
  ren r (lam M) = lam (ren (bindRen r) M)
