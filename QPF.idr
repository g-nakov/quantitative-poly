module QPF

import Linear.Types
import Linear.Equality
import FunExt

{-
   This file implements quantitative polynomial functors as a type
   Desc with interpretation qpf, and shows that initiality implies
   induction for them.
-}


-- Grammar of polynomial functors

public export
data Desc : Type where
  Id' : Desc
  Const' : Type -> Desc
  Prod' : Desc -> Desc -> Desc
  Sum' : Desc -> Desc -> Desc
  With' : Desc -> Desc -> Desc
  Arr' : Type -> Desc -> Desc

-- Interpretation

public export
0 qpf : Desc -> Type -> Type
qpf Id' x = x
qpf (Const' a) _  = a
qpf (Prod' f g) x = LPair (qpf f x) (qpf g x)
qpf (Sum' f g) x = Sum (qpf f x) (qpf g x)
qpf (With' f g) x = With (qpf f x) (qpf g x)
qpf (Arr' a f) x = a -<> qpf f x

public export
fmap : (d : Desc) -> (f : a -<> b) -> qpf d a -<> qpf d b
fmap Id' f x = f x
fmap (Const' _) _ x = x
fmap (Prod' c d) f x = bimap (fmap c f) (fmap d f) x
fmap (Sum' c d) f x = bimap (fmap c f) (fmap d f) x
fmap (With' c d) f x = bimap (fmap c f) (fmap d f) x
fmap (Arr' a c) f x = \ y => fmap c f (x y)

-- Functor laws
0 fmap_id : {d : Desc} -> (1 x : qpf d a) -> x = fmap {b = a} d (\1 x => x) x
fmap_id {d = Id'} x = Refl
fmap_id {d = (Const' _)} _ = Refl
fmap_id {d = (Prod' c d)} (x # y) = lcong2 (#) (fmap_id x) (fmap_id y)
fmap_id {d = (Sum' c d)} (Inl x) = lcong Inl (fmap_id x)
fmap_id {d = (Sum' c d)} (Inr y) = lcong Inr (fmap_id y)
fmap_id {d = (With' c d)} x = funext (\b => if b then fmap_id (x True) else fmap_id (x False))
fmap_id {d = (Arr' a c)} g = funext (\ y => fmap_id (g y))

0 fmap_comp : (d : Desc) -> {f : a -<> b} -> {g : b -<> c} ->
              (1 x : qpf d a) -> fmap d g (fmap d f x) = fmap d (\ x => g (f x)) x
fmap_comp Id' x = Refl
fmap_comp (Const' a) _ = Refl
fmap_comp (Prod' c d) (x # y) = lcong2 (#) (fmap_comp c {f} {g} x) (fmap_comp d {f} {g} y)
fmap_comp (Sum' c d) (Inl x) = lcong Inl (fmap_comp c x)
fmap_comp (Sum' c d) (Inr y) = lcong Inr (fmap_comp d y)
fmap_comp (With' c d) x = funext (\b => if b then fmap_comp c (x True) else fmap_comp d (x False))
fmap_comp (Arr' a c) g = funext (\ y => fmap_comp c (g y))

-- Predicate lifting

public export
0 lift : (d : Desc) -> (p : x -> Type) -> qpf d x -> Type
lift Id' p f = p f
lift (Const' a) p x = Sigma1 a (\ y => x = y)
lift (Prod' c d) p z = LPair (lift c p (LPair.fst z)) (lift d p (LPair.snd z))
lift (Sum' c d) p z = Sum (Sigma0 (qpf c x) (\ z1 => LPair (z = Inl z1) (lift c p z1))) (Sigma0 (qpf d x) (\ z2 => LPair (z = Inr z2) (lift d p z2)))
lift (With' c d) p f = With (lift c p (f True)) (lift d p (f False))
lift (Arr' a c) p f = (1 y : a) -> lift c p (f y)

-- Lifting fuses with fmap (we only provide the useful direction)

0 liftcomp : (d : Desc) -> (p : x -> Type) -> (g : x' -<> x) ->
           (y : qpf d x') -> lift d p (fmap d g y) -> lift d (\ w => p (g w)) y
liftcomp Id' p g y z = z
liftcomp (Const' a) p g y z = z
liftcomp (Prod' c d) p g (x # y) (z1 # z2) = (liftcomp c p g x z1) # (liftcomp d p g y z2)
liftcomp (Sum' c d) p g (Inl y) (Inl (_ # (Refl # z))) = Inl (y # (Refl # liftcomp c p g y z))
liftcomp (Sum' c d) p g (Inl y) (Inr (_ # (leqr # z))) = absurd leqr
liftcomp (Sum' c d) p g (Inr y) (Inl (_ # (leqr # z))) = absurd (sym leqr)
liftcomp (Sum' c d) p g (Inr y) (Inr (_ # (Refl # z))) = Inr (y # (Refl # liftcomp d p g y z))
liftcomp (With' c d) p g y z = \ b => if b then liftcomp c p g (y True) (z True) else liftcomp d p g (y False) (z False)
liftcomp (Arr' a c) p g f z = \ y => liftcomp c p g (f y) (z y)

liftfmap : (d : Desc) -> {p : x -> Type} ->
           ((1 y : x) -> p y) -> (1 z : qpf d x) -> lift d p z
liftfmap Id' f z = f z
liftfmap (Const' a) f z = z # Refl
liftfmap (Prod' c d) f (z1 # z2) = liftfmap c f z1 # liftfmap d f z2
liftfmap (Sum' c d) f (Inl z) = Inl (z # (Refl # liftfmap c f z))
liftfmap (Sum' c d) f (Inr z) = Inr (z # (Refl # liftfmap d f z))
liftfmap (With' c d) f z = \ b => if b then liftfmap c f (z True) else liftfmap d f (z False)
liftfmap (Arr' a c) f z = \ y => liftfmap c f (z y)

0 liftfmap_comp : {x : Type} -> {x' : Type} -> (d : Desc) -> {p : x -> Type} ->
                (f : (1 y : x) -> p y) -> (g : x' -<> x) ->
                (1 z : qpf d x') ->
                liftcomp d p g z (liftfmap d {p} f (fmap d g z)) = liftfmap d {p = \ w => p (g w)} (\ x => f (g x)) z

liftfmap_comp Id' f g y = Refl
liftfmap_comp (Const' a) f g y = Refl
liftfmap_comp (Prod' c d) f g (x # y) = lcong2 (#) (liftfmap_comp c f g x) (liftfmap_comp d f g y)
liftfmap_comp (Sum' c d) f g (Inl y) = lcong (\ z => Inl (y # (Refl # z))) (liftfmap_comp c f g y)
liftfmap_comp (Sum' c d) f g (Inr y) = lcong (\ z => Inr (y # (Refl # z))) (liftfmap_comp d f g y)
liftfmap_comp (With' c d) f g y =  funext (\ b => if b then liftfmap_comp c f g (y True) else liftfmap_comp d f g (y False))
liftfmap_comp (Arr' a c) f g h = funext (\ y => liftfmap_comp c f g (h y))



-- qpf d distributes over Sigma0

public export
dist : {0 x : Type} -> {0 y : x -> Type} ->
       (d : Desc) -> qpf d (Sigma0 x y) -<> Sigma0 (qpf d x) (lift d y)
dist Id' (x # y)  = x # y
dist (Const' _) x = x # (x # Refl)
dist (Prod' c d) (x # y) =
  let (f # lf) = dist c x
      (g # lg) = dist d y
  in  (f # g) # (lf # lg)
dist (Sum' c d) (Inl f) =
  let (f # lf) = dist c f
  in  (Inl f) # (Inl (f # (Refl # lf)))
dist (Sum' c d) (Inr g) =
  let (g # lg) = dist d g
  in  (Inr g) # (Inr (g # (Refl # lg)))
dist (With' c d) w =
   (h w) # (j w) where
    0 h : With (qpf c (Sigma0 x y)) (qpf d (Sigma0 x y)) -> With (qpf c x) (qpf d x)
    h u True  = fst (dist c (u True))
    h u False = fst (dist d (u False))

    j : (1 u : With (qpf c (Sigma0 x y)) (qpf d (Sigma0 x y))) ->
        With (lift c y (h u True)) (lift d y (h u False))
    j u True  = snd (dist c (u True))
    j u False = snd (dist d (u False))
dist (Arr' a c) w =
   (h w) # (j w) where
    0 h : (a -<> qpf c (Sigma0 x y)) -> (a -<> qpf c x)
    h g z = fst (dist c (g z))

    j : (1 g : a -<> qpf c (Sigma0 x y)) ->
        ((1 z : a) -> (lift c y (h g z)))
    j g z = snd (dist c (g z))

-- The first projection of dist is fmap fst
0 distfst : (d : Desc) -> {0 x : Type} -> {0 p : x -> Type} ->
          (y : qpf d (Sigma0 x p)) -> fst {b = lift d p} (dist {y = p} d y) = fmap {b = x} d (fst {b = p}) y
distfst Id' (x # y) = Refl
distfst (Const' a) y = Refl
distfst (Prod' c d) (x # y) with (distfst c x)
  distfst (Prod' c d) (x # y) | r with (distfst d y)
    distfst (Prod' c d) (x # y) | r | q with (dist c x)
      distfst (Prod' c d) (x # y) | r | q | (f # lf) with (dist d y)
         distfst (Prod' c d) (x # y) | r | q | (f # lf) | (g # lg) = lcong2 (#) r q
distfst (Sum' c d) (Inl y) with (distfst c y)
  distfst (Sum' c d) (Inl y) | q with (dist c y)
    distfst (Sum' c d) (Inl y) | q | (f # lf) = lcong Inl q
distfst (Sum' c d) (Inr y) with (distfst d y)
  distfst (Sum' c d) (Inr y) | q with (dist d y)
    distfst (Sum' c d) (Inr y) | q | (f # lf) = lcong Inr q
distfst (With' c d) y = funext (\ b => if b then distfst c (y True) else distfst d (y False))
distfst (Arr' a c) y = funext (\ z => distfst c (y z))


-- Algebra

public export
data W : (0 u : Desc) -> Type where
  Con : qpf u (W u)  -<> W u
  -- Note: we only use pattern matching on Con to define fold and prove its properties

-- The notion of algebra morphism

0 morphism : (d : Desc) -> (alg1 : qpf d a -<> a) -> (alg2 : qpf d b -<> b) ->
             a -<> b -> Type
morphism d alg1 alg2 f = (1 y : qpf d a) -> f (alg1 y) = alg2 (fmap d f y)

0 morphism_id : (alg : qpf d a -<> a) -> morphism d alg alg (\ x => x)
morphism_id alg y = lcong alg (fmap_id y)

0 morphism_comp : {d : Desc} ->
                  (alg1 : qpf d a -<> a) ->
                  (alg2 : qpf d b -<> b) ->
                  (alg3 : qpf d c -<> c) ->
                  {f : a -<> b} -> {g : b -<> c} ->
                  morphism d alg1 alg2 f ->
                  morphism d alg2 alg3 g ->
                  morphism d alg1 alg3 (\ x => g (f x))
morphism_comp {d} alg1 alg2 alg3 {f} {g} m12 m23 y =
  trans (lcong g (m12 y)) (trans (m23 (fmap d f y)) (lcong alg3 (fmap_comp d y)))

-- Unique mediating morphism

mutual
  fold_h : {c : Desc} -> (d : Desc) -> (qpf c x -<> x) -> qpf d (W c) -<> qpf d x
  fold_h Id' alg (Con w) = alg (fold_h c alg w)
  fold_h (Const' y) alg w = w
  fold_h (Prod' c d) alg w = bimap (fold_h c alg) (fold_h d alg) w
  fold_h (Sum' c d) alg w = bimap (fold_h c alg) (fold_h d alg) w
  fold_h (With' c d) alg w = with With.bimap (bimap (fold_h c alg) (fold_h d alg) w)
  fold_h (Arr' a c) alg w = \ y => fold_h c alg (w y)

  fold : (d : Desc) -> (qpf d x -<> x) -> W d -<> x
  fold d alg (Con w) = alg (fold_h d alg w)

mutual
  0 uniq_h : {c : Desc} -> (d : Desc) ->
             (h : W c -<> x) ->
             (alg : qpf c x -<> x) ->
             morphism c Con alg h ->
             (w : qpf d (W c)) -> fmap d h w = fold_h {c = c} d alg w
  uniq_h Id' h alg commutes (Con y) = trans (commutes y) (lcong alg (uniq_h c h alg commutes y))
  uniq_h (Const' y) h calg commutes z = Refl
  uniq_h (Prod' c' d') h calg commutes (f' # g') =
    let uc' = uniq_h c' h calg commutes f'
        ud' = uniq_h d' h calg commutes g'
    in lcong2 (#) uc' ud'
  uniq_h (Sum' c' d') h calg commutes (Inl f') = lcong Inl (uniq_h c' h calg commutes f')
  uniq_h (Sum' c' d') h calg commutes (Inr g') = lcong Inr (uniq_h d' h calg commutes g')
  uniq_h (With' c' d') h calg commutes z =
    funext (\x => if x then uniq_h c' h calg commutes (z True)
                       else uniq_h d' h calg commutes (z False))
  uniq_h (Arr' a c') h calg commutes z = funext (\ y => uniq_h c' h calg commutes (z y))

  0 uniq : {d : Desc} ->
           (alg : qpf d x -<> x) ->
           (h : W d -<> x) ->
           ((1 y : qpf d (W d)) -> h (Con y) = alg (fmap d h y)) ->
           (w : W d) -> h w = fold d alg w
  uniq alg h commutes (Con y) =
    trans (commutes y) (lcong alg (uniq_h d h alg commutes y))

0 foldCon_id : (1 w : W d) -> w = fold d Con w
foldCon_id w = uniq Con (\x => x) (\y => lcong Con (fmap_id y)) w

0 foldCommutes : (d : Desc) -> (alg : qpf d x -<> x) ->
                 morphism d Con alg (fold d alg)
foldCommutes Id' alg (Con x) = Refl
foldCommutes (Const' _) alg x = Refl
foldCommutes (Prod' c d) alg (x # y) =
  let commutesC = uniq_h c (fold (Prod' c d) alg) alg (foldCommutes (Prod' c d) alg) x
      commutesD = uniq_h d (fold (Prod' c d) alg) alg (foldCommutes (Prod' c d) alg) y
  in lcong alg (lcong2 (#) (sym commutesC) (sym commutesD))

foldCommutes (Sum' c d) alg (Inl x) =
  let commutesC = uniq_h c (fold (Sum' c d) alg) alg (foldCommutes (Sum' c d) alg) x
  in lcong alg (lcong Inl (sym commutesC))

foldCommutes (Sum' c d) alg (Inr y) =
  let commutesD = uniq_h d (fold (Sum' c d) alg) alg (foldCommutes (Sum' c d) alg) y
  in lcong alg (lcong Inr (sym commutesD))

foldCommutes (With' c d) alg x =
  lcong alg (funext (\b => if b then sym (uniq_h c (fold (With' c d) alg) alg (foldCommutes (With' c d) alg) (x True))
                else sym (uniq_h d (fold (With' c d) alg) alg (foldCommutes (With' c d) alg) (x False))
     ))
foldCommutes (Arr' a c) alg g =
   lcong alg (funext (\ y => sym (uniq_h c (fold (Arr' a c) alg) alg (foldCommutes (Arr' a c) alg) (g y))))

-- Induction from initiality

pAlg : {d : Desc} -> {0 p : x -> Type} -> (alg : qpf d x -<> x) ->
       (step : (1 w : Sigma0 (qpf d x) (lift d p)) -> p (alg (fst w))) ->
       qpf d (Sigma0 x p) -<> Sigma0 x p
pAlg alg step y = let z = dist d y in alg (fst z) # step z

0 fstCommutes : (d : Desc) -> {0 p : x -> Type} -> {alg : qpf d x -<> x} ->
                {step : (1 w : Sigma0 (qpf d x) (lift d p)) -> p (alg (fst w))} ->
                morphism d (pAlg {d} {p} alg step) alg Sigma0.fst
fstCommutes d z = lcong alg (distfst d z)

public export
induction : {d : Desc} -> {0 p : W d -> Type} ->
            (step : (1 w : Sigma0 (qpf d (W d)) (lift d p)) -> p (Con (fst w))) ->
            (1 w : W d) -> p w
induction step w =
  let
    h : W d -<> Sigma0 (W d) p
    h = fold d (pAlg Con step)
    0 eq : (w : W d) -> fst (h w) = w
    eq w = trans (uniq Con (\w => fst (h w)) (\ y => morphism_comp Con (pAlg Con step) Con (foldCommutes d (pAlg Con step)) (fstCommutes {alg = Con} {step} d) y) w) (sym (foldCon_id w))
  in replace {x = fst (h w)} {p = p} (eq w) (snd (h w))
