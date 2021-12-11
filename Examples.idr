module Examples

import Linear.Equality
import Linear.Types
import Data.Fin
import Data.Nat
import QPF
import QCont


-- Example 12
namespace ListAsQCont

  ListCont : Type -> Type
  ListCont = F Nat Fin

  MaybeCont : Type -> Type
  MaybeCont = F Bool (\b => if b then I else Fin 0)

  Just : x -<> MaybeCont x
  Just x = True # (\Star => x)

  Nothing : (Fin 0 -<> x) -<> MaybeCont x
  Nothing f = False # f

  head : ListCont x -<> MaybeCont x
  head (0 # f) = Nothing f
  head (S n # f) = Just (f 0)

-- Example 21
namespace NatAsQPF

  NatF : Desc
  NatF = Sum' (Const' I) Id'

  N : Type
  N = W NatF

  Zero : N
  Zero = Con (Inl Star)

  Suc : N -> N
  Suc n = Con (Inr n)

  elim : (0 p : N -> Type) -> p Zero -> ((0 n : N) -> p n -<> p (Suc n)) ->
         (1 n : N) -> p n
  elim p p0 ps = induction {p = p} f where
    f : (1 w : Sigma0 (qpf NatF N) (lift NatF p)) -> p (Con (fst w))
    f (_ # (Inl (Star # (Refl # (Star # Refl))))) = p0
    f (_ # (Inr (b # (Refl # ih)))) = ps b ih

-- Example 22
namespace BinTreeAsQPF
  parameters (a : Type)

    BtF : Desc
    BtF = Sum' (Const' a) (Prod' Id' Id')

    Tree : Type
    Tree = W BtF

    Leaf : a -<> Tree
    Leaf x = Con (Inl x)

    Node : Tree -<> Tree -<> Tree
    Node l r = Con (Inr (l # r))


    elim : (0 p : Tree -> Type) ->
           (pl : (1 x : a) -> p (Leaf x)) ->
           (pn : (0 l : Tree) -> (0 r : Tree) -> p l -<> p r -<> p (Node l r)) ->
           (1 t : Tree) -> p t
    elim p pl pn = induction {p = p} f where
      f : (1 w : Sigma0 (qpf BtF Tree) (lift BtF p)) -> p (Con (fst w))
      f (_ # Inl (x # (Refl # (x # Refl)))) = pl x
      f (x # Inr (w # (q # (ihl # ihr)))) = replace1 (\ y => p (Con y)) (eq x w q) (pn _ _ ihl ihr)
        where
        eq : (0 x : Sum a (LPair (W (Sum' (Const' a) (Prod' Id' Id'))) (W (Sum' (Const' a) (Prod' Id' Id'))))) ->
             (0 w : LPair (W (Sum' (Const' a) (Prod' Id' Id'))) (W (Sum' (Const' a) (Prod' Id' Id')))) ->
             (1 q : x = Inr w) -> Inr (fst w # snd w) = x
        eq (Inr (w1 # w2)) (w1 # w2) Refl = Refl
