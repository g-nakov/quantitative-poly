module Linear.Types

public export
(-<>) : Type -> Type -> Type
(-<>) a b = (1 x : a) -> b

infixr 0 -<>

public export
interface LBifunctor f where
  bimap : (a -<> c) -> (b -<> d) -> f a b -<> f c d

namespace LPair

  public export
  0 fst : LPair a b -> a
  fst (x # y) = x

  public export
  0 snd : LPair a b -> b
  snd (x # y) = y

  public export
  0 surjPairing : (w : LPair a b) -> fst w # snd w = w
  surjPairing (x # y) = Refl

public export
LBifunctor LPair where
  bimap f g (x # y) = (f x) # (g y)

public export
data I : Type where
 Star : I

namespace Sigma1
  public export
  data Sigma1 : (a : Type) -> (b : a -> Type) -> Type where
    (#) : (1 x : a) -> (1 y : b x) -> Sigma1 a b

namespace Sigma0
  public export
  data Sigma0 : (a : Type) -> (b : a -> Type) -> Type where
    (#): (0 x : a) -> (1 y : b x) -> Sigma0 a b

  public export
  0 fst : Sigma0 a b -<> a
  fst (x # y) = x

  public export
  snd : (1 x : Sigma0 a b) -> b (fst x)
  snd (x # y) = y

public export
data Sum : (a : Type) -> (b : Type) -> Type where
  Inl : (1 x : a) -> Sum a b
  Inr : (1 y : b) -> Sum a b

public export
Uninhabited (Inl x = Inr y) where
  uninhabited p impossible

public export
LBifunctor Sum where
 bimap f g (Inl x) = Inl $ f x
 bimap f g (Inr y) = Inr $ g y

namespace With
  public export
  0 With : Type -> Type -> Type
  With a b = (1 x : Bool) -> if x then a else b

  public export
  bimap : (a -<> c) -> (b -<> d) -> With a b -<> With c d
  bimap f g x True  = f (x True)
  bimap f g x False = g (x False)


namespace DWith
  public export
  0 DWith : (a : Type) -> (b : a -> Type) -> Type
  DWith a b = Sigma0 a (\x => With (Sigma1 a (\z => z = x)) (b x))

  public export
  fstW : DWith a b -<> a
  fstW (_ # w) = let (z # Refl) = (w True) in z

  public export
  sndW : (1 w : DWith a b) -> b (fstW {b = b} w)
  sndW (x # w) = replace {p = b} (eq (x # w)) (w False)
  where
    eq : (w : DWith a b) -> fst w = fstW {b = b} w
    eq (x # w) with (w True)
      eq (z # w) | (z # Refl) = Refl











