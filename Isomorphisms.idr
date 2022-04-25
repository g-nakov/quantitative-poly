module Isomorphisms

import Linear.Types
import FunExt

-- Isomorphisms in the category of types and linear functions
record Iso a b where
  constructor MkIso
  to : a -<> b
  from : b -<> a
  0 toFrom : (0 y : b) -> to (from y) = y
  0 fromTo : (0 x : a) -> from (to x) = x

-- Identity isomorphism
idIso : Iso a a
idIso = MkIso (\ x => x) (\ x => x) (\ x => Refl) (\ x => Refl)

-- Composition of isomorphisms
transIso : Iso a b -> Iso b c -> Iso a c
transIso f g = MkIso (\ x => to g (to f x))
                     (\ x => from f (from g x))
                     (\ x => rewrite toFrom f (from g x) in toFrom g x)
                     (\ x => rewrite fromTo g (to f x) in fromTo f x)

-- "Dependent pairs are left adjoint to dependent functions" -- true
-- for arbitrary resource annotation ρ, but can only be stated for ρ =
-- 0, 1, ω^< in Idris 2. Here we state it for the most interesting
-- case ρ = ω^<.
curryuncurry : {c : Sigma1 a b -> Type} ->
               Iso ((1 xy : Sigma1 a b) -> c xy) ((1 x : a) -> (1 y : b x) -> c (x # y))
curryuncurry = MkIso (\ f => \ x => \ y => f (x # y))
                     (\ g => \ (x # y) => g x y)
                     (\ f => Refl)
                     (\ g => funext (\ (x # y) => Refl))

pairUnitL : Iso (Sigma1 I b) (b Star)
pairUnitL = MkIso (\ (Star # a) => a)
                  (\ a => Star # a)
                  (\ x => Refl)
                  (\ (Star # a) => Refl)

data Box : Type -> Type where
  Unrestricted : a -> Box x

{-
-- The rules for Top refer to arbitrary contexts, so they
-- cannot be formulated inside Idris 2 itself.

zeroInitial : Iso (Void -<> a) Top
zeroInitial = MkIso (\ f => Star)
                    (\ x => \ y => void1 y)
                    (\ x => ?Refl)
                    (\ x => funext (\ y => void1 y))
-}

trivArgument : Iso (I -<> a) a
trivArgument = MkIso (\ f => f Star)
                     (\ a => \ Star => a)
                     (\ a => Refl)
                     (\ f => funext (\ Star => Refl))

-- With our encoding of With a a, this is almost a tautology
twoArgument : Iso (Bool -<> a) (With a a)
twoArgument = MkIso (\ f => \ b => if b then f True else f False)
                    (\ aa => \ b => if b then aa True else aa False)
                    (\ f => funext (\ b => if b then Refl else Refl))
                    (\ aa => funext (\ b => if b then Refl else Refl))
