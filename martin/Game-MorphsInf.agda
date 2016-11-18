{-# OPTIONS --no-termination-check #-}
-- This is because we've yet to rewrite some definitions in a
-- guarded form. We know how to do this, but it will just blow
-- up the definitions a lot.
-- Uncomment this option to see where the problems still are

module Game-MorphsInf where
-- in which we describe many copycat-shaped strategies

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Coinduction

open import Game-CoreInf

dist01 : ∀ {M} → (I ⊘ M) ≈ I
dist01 {gam f} = bsm (sim ⊥-elim λ())
                     (sim ⊥-elim λ())

dist02 : ∀ {P} → (P ⊸ I) ≈ I
dist02 {gam f} = bsm (sim ⊥-elim λ())
                     (sim ⊥-elim λ())

mutual
  unit⊸₁ : ∀ {M} → (I ⊸ M) ≲ M
  unit⊸₁ {gam f} = sim id (λ m → ♯ unit⊗₂)

  unit⊸₂ : ∀ {M} → M  ≲ (I ⊸ M) 
  unit⊸₂ {gam f} = sim id (λ m → ♯ unit⊗₁)
 
  unit⊗₁ : ∀ {M} → (M ⊗ I) ≲ M
  unit⊗₁ {gam {i} f} = sim [ id , ⊥-elim ] (λ m → aux {i} f m)

  unit⊗₂ :  ∀ {M} → M ≲ (M ⊗ I)
  unit⊗₂ {gam f} = sim inj₁ (λ m → ♯ unit⊸₁)

  aux : ∀ {i} (f : T i → ∞ Game) → (i' : T i ⊎ ⊥)
     → ∞ (gam {i} f ▸ ([_,_] {A = T i} {B = ⊥} {C = λ _ → T i} id ⊥-elim i')
              ≲ (gam {i} f) ⊗ I ▸ i')
  aux f (inj₁ x) = ♯ (unit⊸₂ {♭ (f x)})
  aux _ (inj₂ ())

unit⊸ : ∀ {M} → (I ⊸ M) ≈ M
unit⊸ = bsm unit⊸₁ unit⊸₂

unit⊗ : ∀ {M} → (M ⊗ I) ≈ M
unit⊗ = bsm unit⊗₁ unit⊗₂

unit⊘ : ∀ {M} → M ⊘ I ≈ M
unit⊘ {gam f} = bsm (sim id (λ i → ♯ (wk₂ $ unit⊸)))
                    (sim id (λ i → ♯ (wk₁ $ unit⊸)))

sym⊗ : ∀ {M N} → (M ⊗ N) ≈ (N ⊗ M)
sym⊗ {gam f} {gam g}
   = bsm (sim [ inj₂ , inj₁ ]
              [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ])
         (sim [ inj₂ , inj₁ ]
              [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ])

dist10 : ∀ {M} → (I ⊗ M) ≈ M
dist10 = sym⊗ ≈∘≈ unit⊗

dec1 : ∀ {M N} → M ⊗ N ≈ (M ⊘ N) ×' (N ⊘ M)
dec1 {gam {i} f} {gam {j} g}
   = bsm (sim id ( [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ] ))
         (sim id ( [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ] ))
-- ♯ id≲

dist1 : ∀ {M N O} → (M ×' N) ⊘ O ≈ (M ⊘ O) ×' (N ⊘ O)
dist1 {gam f} {gam g} {gam h}
    = bsm (sim id [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ])
          (sim id [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ])

dist2 : ∀ {M N O} → O ⊸ (M ×' N) ≈ (O ⊸ M) ×' (O ⊸ N)
dist2 {gam f} {gam g} {gam h}
    = bsm (sim id [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ])
          (sim id [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ])

sym× : ∀ {M N} → M ×' N ≈ N ×' M
sym× {gam f} {gam g}
   = bsm (sim [ inj₂ , inj₁ ] [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ])
         (sim [ inj₂ , inj₁ ] [ (λ _ → ♯ id≲) , (λ _ → ♯ id≲) ])   

lfe : ∀ {M N} → (M ⊸ N) ⊸o ≈ (N ⊸o) ⊘ M
lfe {gam f} {gam g}
  = bsm (sim id (λ _ → ♯ id≲))
        (sim id (λ _ → ♯ id≲))

curryo : ∀ {M N} → M ⊸ (N ⊸o) ≈ (N ⊗ M) ⊸o
curryo {gam f} {gam g}
  = bsm (sim id (λ _ → ♯ id≲))
        (sim id (λ _ → ♯ id≲))

↑≈⊸o : ∀ {M} → M ⊸o ≈ M ⊸ o
↑≈⊸o = bsm (sim (λ _ → tt) (λ _ → ♯ (wk₁ $ sym⊗ ≈∘≈ unit⊗)))
           (sim (λ _ → tt) (λ _ → ♯ (wk₂ $ sym⊗ ≈∘≈ unit⊗)))

-- We can apply isomorphisms underneath actions:

mutual

  -- We can beat the productivity checker here by expanding the
  -- definition of coproduct into an auxillary function with pattern
  -- matching.

  _⊸≲_ : ∀ {M N} O → M ≲ N → (O ⊸ M) ≲ (O ⊸ N)
  _⊸≲_ {gam f} {gam g} (gam h) (sim f' g')
       = sim f' (λ m → ♯ ♭ (g' m) ≲⊗ (gam h))

  _≲⊗_ : ∀ {M N} → M ≲ N → ∀ O → (M ⊗ O) ≲ (N ⊗ O)
  _≲⊗_ {gam {i} f} {gam {j} g} (sim f' g') (gam {k} h) 
       = sim [ inj₁ ∘ f' , inj₂ ] [ (λ m → ♯ gam h ⊸≲ ♭ (g' m)) , 
                                    (λ o' → ♯ (sim f' g') ≲⊸ ♭ (h o'))]

  _≲⊸_ : ∀ {M N} → N ≲ M → ∀ O → (M ⊸ O) ≲ (N ⊸ O)
  _≲⊸_ {gam f} {gam g} s (gam h) =
        sim id (λ o' → ♯ ♭ (h o') ⊗≲ s)

  _⊗≲_ : ∀ {M N} O → M ≲ N → (O ⊗ M) ≲ (O ⊗ N)
  _⊗≲_ {gam f} {gam g} (gam h) (sim f' g') = sim [ inj₁ ,  inj₂ ∘ f' ]
                                  [ ((λ o' → ♯ (sim f' g') ≲⊸ ♭ (h o'))) ,
                                    ((λ m → ♯ gam h ⊸≲ ♭ (g' m))) ]



--(wk₁ $ sym⊗) ≲∘≲ (s ≲⊗ O) ≲∘≲ (wk₁ $ sym⊗)

_≲⊘_ : ∀ {M N} → M ≲ N → ∀ O → (M ⊘ O) ≲ (N ⊘ O)
_≲⊘_ {gam f} {gam g} (sim f' g') (gam h)
     = sim f' (λ m → ♯ gam h ⊸≲ ♭ (g' m))

_⊘≲_ : ∀ {M N} O → M ≲ N → (O ⊘ M) ≲ (O ⊘ N)
(gam o) ⊘≲ s = sim id (λ m → ♯ s ≲⊸ ♭ (o m))

_⊗≈_ : ∀ {M N} O → M ≈ N → (O ⊗ M) ≈ (O ⊗ N)
O ⊗≈ s = bsm (O ⊗≲ wk₁ s) (O ⊗≲ wk₂ s)

_≈⊘_ : ∀ {M N} → M ≈ N → ∀ O → (M ⊘ O) ≈ (N ⊘ O)
s ≈⊘ O = bsm (wk₁ s ≲⊘ O) (wk₂ s ≲⊘ O)

_⊘≈_ : ∀ {M N} O → M ≈ N → O ⊘ M ≈ O ⊘ N
O ⊘≈ s = bsm (O ⊘≲ (wk₁ s)) (O ⊘≲ (wk₂ s))

_⊸≈_ : ∀ {M N} O → M ≈ N → (O ⊸ M) ≈ (O ⊸ N)
O ⊸≈ s = bsm (O ⊸≲ (wk₁ s)) (O ⊸≲ (wk₂ s))

_≈⊸_ : ∀ {M N} → M ≈ N → ∀ O → (M ⊸ O) ≈ (N ⊸ O)
s ≈⊸ O = bsm (wk₂ s ≲⊸ O) (wk₁ s ≲⊸ O)

mutual

  -- To beat the Productivity checker on this definition, one must:

  --    1) Replace the use of copairings [ , ] with auxilary functions
  --    and pattern matching

  --    2) Replace the use of sym⊗ and sym⊸ with extra copies of the
  --    entire thing (cf with strategy composition) which probably
  --    means doubling everything that's otherwise there with very
  --    similar code. For example, in the case of pasc⊸ one must swap
  --    M and N on the RHS.

  --    3) Divide each function into two copies showing ≲ and ≳
  --    removing the use of arbitrary functions wk₁ and wk₂ (as
  --    above).

  -- Resultantly pasc⊸ gets replaced by 4 functions
  -- One copy of asc⊗ gets 4 auxillary functions, and then gets
  -- multiplied by 4 (each direction, symmetry) so asc⊗ is replaced by
  -- 20 mutually recursive functions
  -- Psym⊸ is removed from the mutual definition. 

  -- But anyway, 2 mutually recursive functions must be replaced for
  -- 24...

  pasc⊸ : ∀ {M N O} → M ⊸ (N ⊸ O) ≈ (M ⊗ N) ⊸ O
  pasc⊸ {gam m} {gam n} {gam o}
      = bsm (sim id (λ i → ♯ ((♭ (o i) ⊗≲ (wk₁ $ sym⊗)) ≲∘≲
                           (wk₂ $ asc⊗ {♭ $ o i} {gam n} {gam m}))))
            (sim id (λ i → ♯ ((wk₁ $ asc⊗ {♭ $ o i} {gam n} {gam m}) ≲∘≲
                           (♭ (o i) ⊗≲ (wk₂ $ sym⊗)))))

  asc⊗ : ∀ {M N O} → (M ⊗ N) ⊗ O ≈ M ⊗ (N ⊗ O)
  asc⊗ {gam m} {gam n} {gam o}
     = bsm (sim [ [ inj₁ , inj₂ ∘ inj₁ ] , inj₂ ∘ inj₂ ]
                [ [ (λ i → ♯ ((wk₁ (sym⊗) ≲⊸ (♭ $ m i)) ≲∘≲
                           (wk₂ $ pasc⊸ {gam o} {gam n} {♭ $ m i})))
                  , (λ i → ♯ (wk₁ $ psym⊸ {gam m} {gam o} {♭ $ n i})) ]
                  , (λ i → ♯ (wk₁ $ pasc⊸ {gam m} {gam n} {♭ $ o i})) ])
           (sim [ inj₁ ∘ inj₁ , [ inj₁ ∘ inj₂ , inj₂ ] ]
                [ (λ i → ♯ ((wk₁ $ pasc⊸ {gam o} {gam n} {♭ $ m i}) ≲∘≲
                              (wk₂ (sym⊗) ≲⊸ (♭ $ m i))))
                , [ (λ i → ♯ (wk₁ $ psym⊸ {gam o} {gam m} {♭ $ n i}))
                  , (λ i → ♯ (wk₂ $ pasc⊸ {gam m} {gam n} {♭ $ o i})) ] ])

  psym⊸ : ∀ {M N O} → M ⊸ (N ⊸ O) ≈ N ⊸ (M ⊸ O)
  psym⊸ = pasc⊸ ≈∘≈ (sym⊗ ≈⊸ _) ≈∘≈ (pasc⊸ ^-1)

pasc⊘ : ∀ {M N O} → (M ⊘ N) ⊘ O ≈ M ⊘ (N ⊗ O)
pasc⊘ {gam m} {gam n} {gam o}
    = bsm (sim id (λ i → ♯ ((wk₁ (sym⊗) ≲⊸ (♭ $ m i)) ≲∘≲ (wk₂ $ pasc⊸))))
          (sim id (λ i → ♯ ((wk₁ $ pasc⊸) ≲∘≲ (wk₁ (sym⊗) ≲⊸ (♭ $ m i)))))

psym⊘ : ∀ {M N O} → (M ⊘ N) ⊘ O ≈ (M ⊘ O) ⊘ N
psym⊘ = pasc⊘ ≈∘≈ (_ ⊘≈ sym⊗) ≈∘≈ (pasc⊘ ^-1)

mutual
  ≲⊗af : ∀ {M N} → M ≲ M ⊗ N
  ≲⊗af {gam g} {gam _} = sim inj₁ (λ m → ♯ (≲⊸af {♭ $ g m}))

  ≲⊸af : ∀ {M N} → N ⊸ M ≲ M
  ≲⊸af {gam g} = sim id (λ m → ♯ (≲⊗af {♭ $ g m}))

≲⊘af : ∀ {M N} → M ≲ M ⊘ N
≲⊘af {gam _} = sim id (λ m → ♯ ≲⊸af)

≲wk : ∀ {M N} → M ⊘ N ≲ M ⊗ N
≲wk {gam _} {gam _} = sim inj₁ (λ x → ♯ id≲)

≲I : ∀ {M} → I ≲ M
≲I = sim ⊥-elim (λ())

≲π₁ : ∀ {M N} → M ≲ M ×' N
≲π₁ {gam _} {gam _} = sim inj₁ (λ _ → ♯ id≲)

≲π₂ : ∀ {M N} → N ≲ M ×' N
≲π₂ {gam _} {gam _} = sim inj₂ (λ _ → ♯ id≲)

⊸≲⊸̂ : ∀ {M N} → M ⊸ N ≲ M ⊸̂ N
⊸≲⊸̂ {gam m} {gam n} = sim id (λ n' → ♯ (≲wk {gam m} {♭ $ n n'} ≲∘≲ (wk₁ sym⊗)))
