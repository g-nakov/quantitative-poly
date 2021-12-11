module QCont

import Linear.Types
import Linear.Equality
import FunExt

import Syntax.PreorderReasoning

{-
   This file implements quantitative containers, and shows the
   equivalence of initiality and induction for them.

   For convenience, we use an Idris data type to implement the
   underlying algebra and pattern matching to implement the mediating
   morphism fold, as this gives us definitional commutation rules for it.
-}

-- We fix as parameters the shape and position types
parameters (S : Type, P : S -> Type)

  -- Quantative Container || S <| P || interpretation as a functor
  public export
  F : Type -> Type
  F x = Sigma1 S (\ s => P s -<> x)

  infix 10 <$#>

  -- F is functorial
  (<$#>) : (f : x -<> y) -> (F x -<> F y)
  f <$#> (a # h) = a # (\ z => f (h z))

  alg : Type -> Type
  alg x = F x -<> x

  -- Type for initial algebra; we only use pattern matching to define fold
  data W : Type where
    Con : F W -<> W

  -- F-algebra homomorphisms
  infix 10 ==>
  infix 10 #
  data (==>) : alg x -> alg y -> Type where
    (#) : {alpha : alg x} -> {beta : alg y} ->
          (1 fun : x -<> y) ->
          (0 commutes : (arg : F x) -> fun (alpha arg) = beta (fun <$#> arg)) ->
          alpha ==> beta

  -- extracting the underlying function of the morphism
  fun : {alpha : alg x} -> {beta : alg y} -> (1 h : alpha ==> beta) -> x -<> y
  fun (f # _) = f

  -- extracting the proof that it commutes
  0 commutes : {alpha : alg x} -> {beta : alg y} -> (h : alpha ==> beta) ->
             (arg : F x) -> fun h (alpha arg) = beta (fun h <$#> arg)
  commutes ( _ # c) = c

  -- Equality of morphisms
  infix 10 =@
  0  (=@) : {alpha : alg x} -> {beta : alg y} -> (f , g : alpha ==> beta) -> Type
  f =@ g  = (arg : x) -> fun f arg = fun g arg

  0 eq_H_from_fun : {alpha : alg x} -> {beta : alg y} ->
                    (h, g : alpha ==> beta) -> h =@ g -> h = g
  eq_H_from_fun (h # commh) (g # commg) eqp with (funextW eqp)
    eq_H_from_fun (h # commh) (h # commg) eqp | Refl = lcong (\comm => h # comm) eq_comm
      where
      0 eq_comm : commh = commg
      eq_comm = funextW (\x => uip (commh x) (commg x))

  -- composition of F-algebra homomorphisms is an F-algebra homomorphism
  infix 10 .&
  (.&) : {alpha : alg x} -> {beta : alg y} -> {gamma : alg z} ->
         (beta ==> gamma) -> (alpha ==> beta) -> alpha ==> gamma
  (h # commh) .& (g # commg) = (\ 1 x => h (g x)) # comm
    where
     0 comm : (x : F x) -> h (g (alpha x)) = gamma ((\1 x => h (g x)) <$#> x)
     comm x@(s # p) = rewrite commg x in commh (g <$#> x)

  -- identity homomorphism
  id_H : (alpha : alg x) -> alpha ==> alpha
  id_H alpha = (\1 x => x) # \ (s # p) => Refl

  -- mediating map out of mu F
  fold : (alpha : alg x) -> Con ==> alpha
  fold alpha = f # \ (s # h) => Refl
    where
     f : W -<> x
     f (Con (s # h)) = alpha (s # \ p => f (h p))

  -- uniqueness of the mediating map fold
  0 uniqueness : {alpha : alg x} -> (g : Con ==> alpha) -> g = fold alpha
  uniqueness {alpha} g = eq_H_from_fun g (fold alpha) (uniq_f g)
    where
    uniq_f : {alpha : alg x} -> (g : Con ==> alpha) -> g =@ fold alpha
    uniq_f {alpha} (g # comm) (Con (s # h)) =
      trans (comm (s # h)) (cong (\ h => alpha (s # h)) (funext pointwise))
        where
        0 pointwise : (1 x : P s) -> g (h x) = fun (fold alpha) (h x)
        pointwise p = uniq_f (g # comm) (h p)


  -- fold to muF is identity
  0 id_H_eq_foldW : id_H Con = fold Con
  id_H_eq_foldW = uniqueness (id_H Con)

  -- induction principle from initiality
  parameters (0 Q : W -> Type)

    ind_alg : ((1 s : S) -> (0 h : P s -<> W) ->
               ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) -<>
             alg (Sigma0 W Q)
    ind_alg m (s # h) = Con (fst <$#> (s # h)) # m s _ (\1 p => snd (h p))

    0 fst_ind_alg : ((1 s : S) -> (0 h : P s -<> W) ->
                     ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) -<>
                    Con ==> Con
    fst_ind_alg m =  (\1 w => fst (fun (fold (ind_alg m)) w)) # \(s # h) => Refl

    0 id_H_eq_fia : (1 m : (1 s : S) -> (0 h : P s -<> W) ->
                     ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) ->
                  (id_H Con = fst_ind_alg m)
    id_H_eq_fia m = trans id_H_eq_foldW (sym (uniqueness (fst_ind_alg m)))

    0 id_P_eq_fia : (1 m : (1 s : S) -> (0 h : P s -<> W) ->
                     ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) ->
                    (id_H Con =@ fst_ind_alg m)
    id_P_eq_fia m w = lcongApp (lcong fun (id_H_eq_fia m)) w

    public export
    induction : ((1 s : S) -> (0 h : P s -<> W) ->
                 ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) ->
                (1 w : W) -> Q w
    induction m w = replace {p = Q} (sym (id_P_eq_fia m w)) (snd (fun (fold (ind_alg m)) w))

  -- computation rule
  0 ind_comp : (0 Q : W -> Type) ->
               (m : (1 s : S) -> (0 h : P s -<> W) ->
                 ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) ->
               (1 s : S) -> (0 h : P s -<> W) ->
               induction Q m (Con (s # h)) = m s h (\1 p => induction Q m (h p))
  ind_comp q m s h =  Calc $
    |~ induction q m (Con (s # h))
    ~~ m s h (\p => induction q m (h p))  ...(fixQ eq snd_fold)
   where
     0 fixQ : {g : W -<> W} -> (eq : (\1 x => x) = g) -> (exp : (0 w : W) -> q (g w)) ->
               replace {p = q} (sym (cong (\ g => Con (s # (\z => g (h z)))) eq))
                        (m s (\ z => g (h z)) (\1 p => exp (h p)))
              = m s h (\1 p => replace {p = q} (sym (lcongApp eq (h p))) (exp (h p)))
     fixQ Refl v = Refl

     0 fst_fold : W -<> W
     fst_fold w = fst (fun (fold (ind_alg q m)) w)

     snd_fold : (0 w : W) -> q (fst_fold w)
     snd_fold w = snd (fun (fold (ind_alg q m)) w)

     0 eq : (\1 w => w) = (\1 w => fst_fold w)
     eq = lcong fun (id_H_eq_fia q m)

  -- initiality out of induction
  initiality : (alpha : alg x) -> Con ==> alpha
  initiality alpha = (induction (\ _ => x) (\ s , _ , ih  => alpha (s # ih))) # eq
    where
      0 eq : (w : F W) ->
             induction (\ _ => x) (\ s , _ , ih => alpha (s # ih)) (Con w) =
             alpha (induction (\ _ => x) (\ s , _, ih => alpha (s # ih)) <$#> w)
      eq (s # h) = ind_comp (\ _ => x) (\s, _, ih => alpha (s # ih)) s h

  0 uniq_morphism_f : (alpha : alg x) -> (f : Con ==> alpha) ->
                      fun f = fun (initiality alpha)
  uniq_morphism_f alpha (f # comm) = funext (induction (\ z => f z = fun (initiality alpha) z) m)
    where
      0 ihp : (1 s : S) -> (0 h : P s -<> W) ->
              (1 ih : (1 p : P s) -> f (h p) = fun (initiality alpha) (h p)) ->
              (1 p : P s) ->
              f (h p) =  induction (\ _ => x) (\ s, _, ih => alpha (s # ih)) (h p)
      ihp s h ih p = ih p

      0 m : (1 s : S) -> (0 h : P s -<> W) -> (1 ih : (1 p : P s) -> f (h p) = fun (initiality alpha) (h p)) ->
           f (Con (s # h)) = fun (initiality alpha) (Con (s # h))
      m s h ih = Calc $
       |~ f (Con (s # h))
       ~~ alpha (s # \1 x => f (h x))
          ...(comm (s # h))
       ~~ alpha (s # \p => fun (initiality alpha) (h p))
          ...( cong (\ u => alpha (s # u))
                    (funext (ihp s h ih)))
       ~~ fun (initiality alpha) (Con (s # h))
          ...( sym (ind_comp (\ _ => x) (\s , _ , h => alpha (s # h)) s h))

  0 uniq_morphism_h : (alpha : alg x) -> (f : Con ==> alpha) -> f = initiality alpha
  uniq_morphism_h alpha f = eq_H_from_fun f (initiality alpha) (lcongApp (uniq_morphism_f alpha f))
